Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_LREC_term_abbrevs.
Require Import EXTENSION_spec.
Require Import INT_POS_spec.
Require Import IN_INSERT_spec.
Require Import numseg_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem5351284 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5351285 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem5351284 _83095 p). Qed.
Lemma lem5351286 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem5351287 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem5351286 _83095 p) (@lem5351285 _83095 p)). Qed.
Lemma lem5351288 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem5351287 _83095 p x). Qed.
Lemma lem5351289 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem5351298 (m : nat) : term5 m.
Proof. exact (@lem5329077 m). Qed.
Lemma lem5351299 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem5351300 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem5351299 m) (@lem5351298 m)). Qed.
Lemma lem5351301 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem5351300 m n). Qed.
Lemma lem5351302 (m : nat) (n : nat) : (term7 m n) = ((dotdot m n) = (term8 m n)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem5351304 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5351305 {A : Type'} (x : A) : (term9 A x) = (term10 A x).
Proof. exact (eq_refl (term9 A x)). Qed.
Lemma lem5351306 {A : Type'} (x : A) : term10 A x.
Proof. exact (EQ_MP (@lem5351305 A x) (@lem5351304 A x)). Qed.
Lemma lem5351307 {A : Type'} (x : A) (y : A) : term11 A x y.
Proof. exact (@lem5351306 A x y). Qed.
Lemma lem5351308 {A : Type'} (y : A) (x : A) : (term11 A x y) = (term12 A y x).
Proof. exact (eq_refl (term11 A x y)). Qed.
Lemma lem5351309 {A : Type'} (y : A) (x : A) : term12 A y x.
Proof. exact (EQ_MP (@lem5351308 A y x) (@lem5351307 A x y)). Qed.
Lemma lem5351310 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term13 A y x s.
Proof. exact (@lem5351309 A y x s). Qed.
Lemma lem5351311 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term13 A y x s) = ((term14 A x y s) = (term15 A y x s)).
Proof. exact (eq_refl (term13 A y x s)). Qed.
Lemma lem5351313 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5351314 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem5351315 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem5351314 A s) (@lem5351313 A s)). Qed.
Lemma lem5351316 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem5351315 A s t). Qed.
Lemma lem5351317 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem5351332 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem5351317 A s t) (@lem5351316 A s t)). Qed.
Lemma lem5351333 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term20 s t).
Proof. exact (@lem5351332 nat s t). Qed.
Lemma lem5351334 (m : nat) (n : nat) : ((term21 m n) = (dotdot m n)) = (term22 m n).
Proof. exact (@lem5351333 (term21 m n) (dotdot m n)). Qed.
Lemma lem5351344 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term14 A x y s) = (term15 A y x s).
Proof. exact (EQ_MP (@lem5351311 A y x s) (@lem5351310 A y x s)). Qed.
Lemma lem5351345 (y : nat) (x : nat) (s : nat -> Prop) : (term23 x y s) = (term24 y x s).
Proof. exact (@lem5351344 nat y x s). Qed.
Lemma lem5351346 (x : nat) (m : nat) (n : nat) : (term25 x m n) = (term26 x m n).
Proof. exact (@lem5351345 m x (term27 m n)). Qed.
Lemma lem5351354 (m : nat) (n : nat) : (dotdot m n) = (term8 m n).
Proof. exact (EQ_MP (@lem5351302 m n) (@lem5351301 m n)). Qed.
Lemma lem5351355 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (@lem5351354 (term29 m) n). Qed.
Lemma lem5351362 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5351363 (x : nat) (m : nat) (n : nat) : (term30 x m n) = (term31 x m n).
Proof. exact (MK_COMB (@lem5351362 x) (@lem5351355 m n)). Qed.
Lemma lem5351365 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5351289 _83095 p x) (@lem5351288 _83095 p x)). Qed.
Lemma lem5351366 (p : nat -> Prop) (x : nat) : (term32 x p) = (p x).
Proof. exact (@lem5351365 nat p x). Qed.
Lemma lem5351367 (m : nat) (n : nat) (x : nat) : (term33 x m n) = (term34 m n x).
Proof. exact (@lem5351366 (term35 m n) x). Qed.
Lemma lem5351368 (m : nat) (x : nat) (n : nat) : (term34 m n x) = (term36 m x n).
Proof. exact (eq_refl (term34 m n x)). Qed.
Lemma lem5351369 (GEN_PVAR_229 : nat) : (@SETSPEC nat GEN_PVAR_229) = (@SETSPEC nat GEN_PVAR_229).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_229)). Qed.
Lemma lem5351370 (GEN_PVAR_229 : nat) (m : nat) (x : nat) (n : nat) : (term37 GEN_PVAR_229 m n x) = (term38 GEN_PVAR_229 m x n).
Proof. exact (MK_COMB (@lem5351369 GEN_PVAR_229) (@lem5351368 m x n)). Qed.
Lemma lem5351371 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5351372 (GEN_PVAR_229 : nat) (m : nat) (n : nat) (x : nat) : (term39 GEN_PVAR_229 m n x) = (term40 GEN_PVAR_229 m n x).
Proof. exact (MK_COMB (@lem5351370 GEN_PVAR_229 m x n) (@lem5351371 x)). Qed.
Lemma lem5351373 (GEN_PVAR_229 : nat) (m : nat) (n : nat) : (term41 GEN_PVAR_229 m n) = (term42 GEN_PVAR_229 m n).
Proof. exact (fun_ext (fun x : nat => @lem5351372 GEN_PVAR_229 m n x)). Qed.
Lemma lem5351374 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5351375 (GEN_PVAR_229 : nat) (m : nat) (n : nat) : (term43 GEN_PVAR_229 m n) = (term44 GEN_PVAR_229 m n).
Proof. exact (MK_COMB (@lem5351374) (@lem5351373 GEN_PVAR_229 m n)). Qed.
Lemma lem5351376 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (fun_ext (fun GEN_PVAR_229 : nat => @lem5351375 GEN_PVAR_229 m n)). Qed.
Lemma lem5351377 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5351378 (m : nat) (n : nat) : (term47 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem5351377) (@lem5351376 m n)). Qed.
Lemma lem5351379 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5351380 (x : nat) (m : nat) (n : nat) : (term33 x m n) = (term31 x m n).
Proof. exact (MK_COMB (@lem5351379 x) (@lem5351378 m n)). Qed.
Lemma lem5351381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5351382 (x : nat) (m : nat) (n : nat) : (term48 x m n) = (term49 x m n).
Proof. exact (MK_COMB (@lem5351381) (@lem5351380 x m n)). Qed.
Lemma lem5351383 (m : nat) (x : nat) (n : nat) : (term34 m n x) = (term36 m x n).
Proof. exact (eq_refl (term34 m n x)). Qed.
Lemma lem5351384 (m : nat) (x : nat) (n : nat) : ((term33 x m n) = (term34 m n x)) = ((term31 x m n) = (term36 m x n)).
Proof. exact (MK_COMB (@lem5351382 x m n) (@lem5351383 m x n)). Qed.
Lemma lem5351385 (m : nat) (x : nat) (n : nat) : (term31 x m n) = (term36 m x n).
Proof. exact (EQ_MP (@lem5351384 m x n) (@lem5351367 m n x)). Qed.
Lemma lem5351388 (m : nat) (x : nat) (n : nat) : (term30 x m n) = (term36 m x n).
Proof. exact (TRANS (@lem5351363 x m n) (@lem5351385 m x n)). Qed.
Lemma lem5351389 (x : nat) (m : nat) : (term50 x m) = (term50 x m).
Proof. exact (eq_refl (term50 x m)). Qed.
Lemma lem5351390 (m : nat) (x : nat) (n : nat) : (term26 x m n) = (term51 m x n).
Proof. exact (MK_COMB (@lem5351389 x m) (@lem5351388 m x n)). Qed.
Lemma lem5351393 (m : nat) (x : nat) (n : nat) : (term25 x m n) = (term51 m x n).
Proof. exact (TRANS (@lem5351346 x m n) (@lem5351390 m x n)). Qed.
Lemma lem5351394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5351395 (m : nat) (x : nat) (n : nat) : (term52 x m n) = (term53 m x n).
Proof. exact (MK_COMB (@lem5351394) (@lem5351393 m x n)). Qed.
Lemma lem5351397 (m : nat) (n : nat) : (dotdot m n) = (term8 m n).
Proof. exact (EQ_MP (@lem5351302 m n) (@lem5351301 m n)). Qed.
Lemma lem5351404 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5351405 (x : nat) (m : nat) (n : nat) : (term54 x m n) = (term55 x m n).
Proof. exact (MK_COMB (@lem5351404 x) (@lem5351397 m n)). Qed.
Lemma lem5351407 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5351289 _83095 p x) (@lem5351288 _83095 p x)). Qed.
Lemma lem5351408 (p : nat -> Prop) (x : nat) : (term32 x p) = (p x).
Proof. exact (@lem5351407 nat p x). Qed.
Lemma lem5351409 (m : nat) (n : nat) (x : nat) : (term56 x m n) = (term57 m n x).
Proof. exact (@lem5351408 (term58 m n) x). Qed.
Lemma lem5351410 (m : nat) (x : nat) (n : nat) : (term57 m n x) = (term59 m x n).
Proof. exact (eq_refl (term57 m n x)). Qed.
Lemma lem5351411 (GEN_PVAR_229 : nat) : (@SETSPEC nat GEN_PVAR_229) = (@SETSPEC nat GEN_PVAR_229).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_229)). Qed.
Lemma lem5351412 (GEN_PVAR_229 : nat) (m : nat) (x : nat) (n : nat) : (term60 GEN_PVAR_229 m n x) = (term61 GEN_PVAR_229 m x n).
Proof. exact (MK_COMB (@lem5351411 GEN_PVAR_229) (@lem5351410 m x n)). Qed.
Lemma lem5351413 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5351414 (GEN_PVAR_229 : nat) (m : nat) (n : nat) (x : nat) : (term62 GEN_PVAR_229 m n x) = (term63 GEN_PVAR_229 m n x).
Proof. exact (MK_COMB (@lem5351412 GEN_PVAR_229 m x n) (@lem5351413 x)). Qed.
Lemma lem5351415 (GEN_PVAR_229 : nat) (m : nat) (n : nat) : (term64 GEN_PVAR_229 m n) = (term65 GEN_PVAR_229 m n).
Proof. exact (fun_ext (fun x : nat => @lem5351414 GEN_PVAR_229 m n x)). Qed.
Lemma lem5351416 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5351417 (GEN_PVAR_229 : nat) (m : nat) (n : nat) : (term66 GEN_PVAR_229 m n) = (term67 GEN_PVAR_229 m n).
Proof. exact (MK_COMB (@lem5351416) (@lem5351415 GEN_PVAR_229 m n)). Qed.
Lemma lem5351418 (m : nat) (n : nat) : (term68 m n) = (term69 m n).
Proof. exact (fun_ext (fun GEN_PVAR_229 : nat => @lem5351417 GEN_PVAR_229 m n)). Qed.
Lemma lem5351419 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5351420 (m : nat) (n : nat) : (term70 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem5351419) (@lem5351418 m n)). Qed.
Lemma lem5351421 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5351422 (x : nat) (m : nat) (n : nat) : (term56 x m n) = (term55 x m n).
Proof. exact (MK_COMB (@lem5351421 x) (@lem5351420 m n)). Qed.
Lemma lem5351423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5351424 (x : nat) (m : nat) (n : nat) : (term71 x m n) = (term72 x m n).
Proof. exact (MK_COMB (@lem5351423) (@lem5351422 x m n)). Qed.
Lemma lem5351425 (m : nat) (x : nat) (n : nat) : (term57 m n x) = (term59 m x n).
Proof. exact (eq_refl (term57 m n x)). Qed.
Lemma lem5351426 (m : nat) (x : nat) (n : nat) : ((term56 x m n) = (term57 m n x)) = ((term55 x m n) = (term59 m x n)).
Proof. exact (MK_COMB (@lem5351424 x m n) (@lem5351425 m x n)). Qed.
Lemma lem5351427 (m : nat) (x : nat) (n : nat) : (term55 x m n) = (term59 m x n).
Proof. exact (EQ_MP (@lem5351426 m x n) (@lem5351409 m n x)). Qed.
Lemma lem5351430 (m : nat) (x : nat) (n : nat) : (term54 x m n) = (term59 m x n).
Proof. exact (TRANS (@lem5351405 x m n) (@lem5351427 m x n)). Qed.
Lemma lem5351431 (m : nat) (x : nat) (n : nat) : ((term25 x m n) = (term54 x m n)) = ((term51 m x n) = (term59 m x n)).
Proof. exact (MK_COMB (@lem5351395 m x n) (@lem5351430 m x n)). Qed.
Lemma lem5351436 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (fun_ext (fun x : nat => @lem5351431 m x n)). Qed.
Lemma lem5351437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351438 (m : nat) (n : nat) : (term22 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem5351437) (@lem5351436 m n)). Qed.
Lemma lem5351443 (m : nat) (n : nat) : ((term21 m n) = (dotdot m n)) = (term75 m n).
Proof. exact (TRANS (@lem5351334 m n) (@lem5351438 m n)). Qed.
Lemma lem5351444 (m : nat) (n : nat) : (term76 m n) = (term76 m n).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem5351445 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem5351444 m n) (@lem5351443 m n)). Qed.
Lemma lem5351448 (m : nat) : (term79 m) = (term80 m).
Proof. exact (fun_ext (fun n : nat => @lem5351445 m n)). Qed.
Lemma lem5351449 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351450 (m : nat) : (term81 m) = (term82 m).
Proof. exact (MK_COMB (@lem5351449) (@lem5351448 m)). Qed.
Lemma lem5351455 : term83 = term84.
Proof. exact (fun_ext (fun m : nat => @lem5351450 m)). Qed.
Lemma lem5351456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351457 : term85 = term86.
Proof. exact (MK_COMB (@lem5351456) (@lem5351455)). Qed.
Lemma lem5351462 : term86 = term85.
Proof. exact (SYM (@lem5351457)). Qed.
Lemma lem5351504 (m : nat) (x : nat) (n : nat) : ((term51 m x n) = (term59 m x n)) = ((term51 m x n) = (term59 m x n)).
Proof. exact (eq_refl ((term51 m x n) = (term59 m x n))). Qed.
Lemma lem5351505 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (fun_ext (fun x : nat => @lem5351504 m x n)). Qed.
Lemma lem5351506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351507 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem5351506) (@lem5351505 m n)). Qed.
Lemma lem5351510 (m : nat) (n : nat) : (term76 m n) = (term76 m n).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem5351511 (m : nat) (n : nat) : (term78 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem5351510 m n) (@lem5351507 m n)). Qed.
Lemma lem5351512 (m : nat) : (term80 m) = (term80 m).
Proof. exact (fun_ext (fun n : nat => @lem5351511 m n)). Qed.
Lemma lem5351513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351514 (m : nat) : (term82 m) = (term82 m).
Proof. exact (MK_COMB (@lem5351513) (@lem5351512 m)). Qed.
Lemma lem5351515 : term84 = term84.
Proof. exact (fun_ext (fun m : nat => @lem5351514 m)). Qed.
Lemma lem5351516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351518 : term86 = term86.
Proof. exact (MK_COMB (@lem5351516) (@lem5351515)). Qed.
Lemma lem5351530 (m : nat) (x : nat) (n : nat) : (term87 m x n) = (term88 m x n).
Proof. exact (@lem17045 (term89 m x) (Peano.le x n)). Qed.
Lemma lem5351535 (x : nat) (m : nat) : (term90 x m) = (term90 x m).
Proof. exact (eq_refl (term90 x m)). Qed.
Lemma lem5351536 (m : nat) (x : nat) (n : nat) : (term91 m x n) = (term92 m x n).
Proof. exact (MK_COMB (@lem5351535 x m) (@lem5351530 m x n)). Qed.
Lemma lem5351537 (m : nat) (x : nat) (n : nat) : (term93 m x n) = (term91 m x n).
Proof. exact (@lem17160 (x = m) (term36 m x n)). Qed.
Lemma lem5351538 (m : nat) (x : nat) (n : nat) : (term93 m x n) = (term92 m x n).
Proof. exact (TRANS (@lem5351537 m x n) (@lem5351536 m x n)). Qed.
Lemma lem5351550 (m : nat) (x : nat) (n : nat) : (term94 m x n) = (term95 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem5351553 (m : nat) (x : nat) (n : nat) : (term59 m x n) = (term59 m x n).
Proof. exact (eq_refl (term59 m x n)). Qed.
Lemma lem5351554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5351555 (m : nat) (x : nat) (n : nat) : (term96 m x n) = (term97 m x n).
Proof. exact (MK_COMB (@lem5351554) (@lem5351538 m x n)). Qed.
Lemma lem5351556 (m : nat) (x : nat) (n : nat) : (term98 m x n) = (term99 m x n).
Proof. exact (MK_COMB (@lem5351555 m x n) (@lem5351553 m x n)). Qed.
Lemma lem5351558 (m : nat) (x : nat) (n : nat) : (term100 m x n) = (term100 m x n).
Proof. exact (eq_refl (term100 m x n)). Qed.
Lemma lem5351559 (m : nat) (x : nat) (n : nat) : (term101 m x n) = (term102 m x n).
Proof. exact (MK_COMB (@lem5351558 m x n) (@lem5351550 m x n)). Qed.
Lemma lem5351560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5351561 (m : nat) (x : nat) (n : nat) : (term103 m x n) = (term104 m x n).
Proof. exact (MK_COMB (@lem5351560) (@lem5351559 m x n)). Qed.
Lemma lem5351562 (m : nat) (x : nat) (n : nat) : (term105 m x n) = (term106 m x n).
Proof. exact (MK_COMB (@lem5351561 m x n) (@lem5351556 m x n)). Qed.
Lemma lem5351563 (m : nat) (x : nat) (n : nat) : ((term51 m x n) = (term59 m x n)) = (term105 m x n).
Proof. exact (@lem17784 (term51 m x n) (term59 m x n)). Qed.
Lemma lem5351564 (m : nat) (x : nat) (n : nat) : ((term51 m x n) = (term59 m x n)) = (term106 m x n).
Proof. exact (TRANS (@lem5351563 m x n) (@lem5351562 m x n)). Qed.
Lemma lem5351565 (m : nat) (n : nat) : (term74 m n) = (term107 m n).
Proof. exact (fun_ext (fun x : nat => @lem5351564 m x n)). Qed.
Lemma lem5351566 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351567 (m : nat) (n : nat) : (term75 m n) = (term108 m n).
Proof. exact (MK_COMB (@lem5351566) (@lem5351565 m n)). Qed.
Lemma lem5351569 (m : nat) (n : nat) : (term109 m n) = (term109 m n).
Proof. exact (eq_refl (term109 m n)). Qed.
Lemma lem5351570 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (MK_COMB (@lem5351569 m n) (@lem5351567 m n)). Qed.
Lemma lem5351571 (m : nat) (n : nat) : (term78 m n) = (term110 m n).
Proof. exact (@lem17265 (Peano.le m n) (term75 m n)). Qed.
Lemma lem5351572 (m : nat) (n : nat) : (term78 m n) = (term111 m n).
Proof. exact (TRANS (@lem5351571 m n) (@lem5351570 m n)). Qed.
Lemma lem5351573 (m : nat) : (term80 m) = (term112 m).
Proof. exact (fun_ext (fun n : nat => @lem5351572 m n)). Qed.
Lemma lem5351574 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351575 (m : nat) : (term82 m) = (term113 m).
Proof. exact (MK_COMB (@lem5351574) (@lem5351573 m)). Qed.
Lemma lem5351576 : term84 = term114.
Proof. exact (fun_ext (fun m : nat => @lem5351575 m)). Qed.
Lemma lem5351577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351578 : term86 = term115.
Proof. exact (MK_COMB (@lem5351577) (@lem5351576)). Qed.
Lemma lem5351579 : term86 = term115.
Proof. exact (TRANS (@lem5351518) (@lem5351578)). Qed.
Lemma lem5351580 (m : nat) (x : nat) (n : nat) : (term106 m x n) = (term106 m x n).
Proof. exact (eq_refl (term106 m x n)). Qed.
Lemma lem5351581 (m : nat) (n : nat) : (term107 m n) = (term107 m n).
Proof. exact (fun_ext (fun x : nat => @lem5351580 m x n)). Qed.
Lemma lem5351582 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351583 (m : nat) (n : nat) : (term108 m n) = (term108 m n).
Proof. exact (MK_COMB (@lem5351582) (@lem5351581 m n)). Qed.
Lemma lem5351586 (m : nat) (n : nat) : (term109 m n) = (term109 m n).
Proof. exact (eq_refl (term109 m n)). Qed.
Lemma lem5351587 (m : nat) (n : nat) : (term111 m n) = (term111 m n).
Proof. exact (MK_COMB (@lem5351586 m n) (@lem5351583 m n)). Qed.
Lemma lem5351588 (m : nat) : (term112 m) = (term112 m).
Proof. exact (fun_ext (fun n : nat => @lem5351587 m n)). Qed.
Lemma lem5351589 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351590 (m : nat) : (term113 m) = (term113 m).
Proof. exact (MK_COMB (@lem5351589) (@lem5351588 m)). Qed.
Lemma lem5351591 : term114 = term114.
Proof. exact (fun_ext (fun m : nat => @lem5351590 m)). Qed.
Lemma lem5351592 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351593 : term115 = term115.
Proof. exact (MK_COMB (@lem5351592) (@lem5351591)). Qed.
Lemma lem5351636 : term86 = term115.
Proof. exact (TRANS (@lem5351579) (@lem5351593)). Qed.
Lemma lem5351735 (m : nat) (x : nat) (n : nat) : (term106 m x n) = (term106 m x n).
Proof. exact (eq_refl (term106 m x n)). Qed.
Lemma lem5351736 (m : nat) (n : nat) : (term107 m n) = (term107 m n).
Proof. exact (fun_ext (fun x : nat => @lem5351735 m x n)). Qed.
Lemma lem5351737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351738 (m : nat) (n : nat) : (term108 m n) = (term108 m n).
Proof. exact (MK_COMB (@lem5351737) (@lem5351736 m n)). Qed.
Lemma lem5351747 (m : nat) (n : nat) : (term109 m n) = (term109 m n).
Proof. exact (eq_refl (term109 m n)). Qed.
Lemma lem5351748 (m : nat) (n : nat) : (term111 m n) = (term111 m n).
Proof. exact (MK_COMB (@lem5351747 m n) (@lem5351738 m n)). Qed.
Lemma lem5351749 (m : nat) : (term112 m) = (term112 m).
Proof. exact (fun_ext (fun n : nat => @lem5351748 m n)). Qed.
Lemma lem5351750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351751 (m : nat) : (term113 m) = (term113 m).
Proof. exact (MK_COMB (@lem5351750) (@lem5351749 m)). Qed.
Lemma lem5351752 : term114 = term114.
Proof. exact (fun_ext (fun m : nat => @lem5351751 m)). Qed.
Lemma lem5351753 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351754 : term115 = term115.
Proof. exact (MK_COMB (@lem5351753) (@lem5351752)). Qed.
Lemma lem5351755 : term86 = term115.
Proof. exact (TRANS (@lem5351636) (@lem5351754)). Qed.
Lemma lem5351757 {A : Type'} (P : Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5351758 (P : Prop) (Q : nat -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem5351757 nat P Q). Qed.
Lemma lem5351759 (m : nat) (n : nat) : (term120 m n) = (term121 m n).
Proof. exact (@lem5351758 (term122 m n) (term107 m n)). Qed.
Lemma lem5351760 (m : nat) (x : nat) (n : nat) : (term123 m n x) = (term106 m x n).
Proof. exact (eq_refl (term123 m n x)). Qed.
Lemma lem5351761 (m : nat) (n : nat) : (term124 m n) = (term107 m n).
Proof. exact (fun_ext (fun x : nat => @lem5351760 m x n)). Qed.
Lemma lem5351762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351763 (m : nat) (n : nat) : (term125 m n) = (term108 m n).
Proof. exact (MK_COMB (@lem5351762) (@lem5351761 m n)). Qed.
Lemma lem5351764 (m : nat) (n : nat) : (term109 m n) = (term109 m n).
Proof. exact (eq_refl (term109 m n)). Qed.
Lemma lem5351765 (m : nat) (n : nat) : (term120 m n) = (term111 m n).
Proof. exact (MK_COMB (@lem5351764 m n) (@lem5351763 m n)). Qed.
Lemma lem5351766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5351767 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem5351766) (@lem5351765 m n)). Qed.
Lemma lem5351768 (m : nat) (x : nat) (n : nat) : (term123 m n x) = (term106 m x n).
Proof. exact (eq_refl (term123 m n x)). Qed.
Lemma lem5351769 (m : nat) (n : nat) : (term109 m n) = (term109 m n).
Proof. exact (eq_refl (term109 m n)). Qed.
Lemma lem5351770 (m : nat) (x : nat) (n : nat) : (term128 m n x) = (term129 m x n).
Proof. exact (MK_COMB (@lem5351769 m n) (@lem5351768 m x n)). Qed.
Lemma lem5351771 (m : nat) (n : nat) : (term130 m n) = (term131 m n).
Proof. exact (fun_ext (fun x : nat => @lem5351770 m x n)). Qed.
Lemma lem5351772 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351773 (m : nat) (n : nat) : (term121 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem5351772) (@lem5351771 m n)). Qed.
Lemma lem5351774 (m : nat) (n : nat) : ((term120 m n) = (term121 m n)) = ((term111 m n) = (term132 m n)).
Proof. exact (MK_COMB (@lem5351767 m n) (@lem5351773 m n)). Qed.
Lemma lem5351775 (m : nat) (n : nat) : (term111 m n) = (term132 m n).
Proof. exact (EQ_MP (@lem5351774 m n) (@lem5351759 m n)). Qed.
Lemma lem5351776 (m : nat) : (term112 m) = (term133 m).
Proof. exact (fun_ext (fun n : nat => @lem5351775 m n)). Qed.
Lemma lem5351777 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351778 (m : nat) : (term113 m) = (term134 m).
Proof. exact (MK_COMB (@lem5351777) (@lem5351776 m)). Qed.
Lemma lem5351779 : term114 = term135.
Proof. exact (fun_ext (fun m : nat => @lem5351778 m)). Qed.
Lemma lem5351780 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351781 : term115 = term136.
Proof. exact (MK_COMB (@lem5351780) (@lem5351779)). Qed.
Lemma lem5351782 : term86 = term136.
Proof. exact (TRANS (@lem5351755) (@lem5351781)). Qed.
Lemma lem5351784 (m : nat) (n : nat) : (Peano.le m n) = (term137 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5351785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5351786 (m : nat) (n : nat) : (term122 m n) = (term138 m n).
Proof. exact (MK_COMB (@lem5351785) (@lem5351784 m n)). Qed.
Lemma lem5351787 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5351788 (m : nat) (n : nat) : (term109 m n) = (term139 m n).
Proof. exact (MK_COMB (@lem5351787) (@lem5351786 m n)). Qed.
Lemma lem5351790 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5351791 (x : nat) (m : nat) : (x = m) = ((int_of_num x) = (int_of_num m)).
Proof. exact (@lem5351790 x m). Qed.
Lemma lem5351794 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5351795 (x : nat) (m : nat) : (term50 x m) = (term140 x m).
Proof. exact (MK_COMB (@lem5351794) (@lem5351791 x m)). Qed.
Lemma lem5351797 (m : nat) (n : nat) : (Peano.le m n) = (term137 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5351798 (m : nat) (x : nat) : (term89 m x) = (term141 m x).
Proof. exact (@lem5351797 (term29 m) x). Qed.
Lemma lem5351800 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5351801 (m : nat) : (term144 m) = (term145 m).
Proof. exact (@lem5351800 m term146). Qed.
Lemma lem5351802 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem5351803 (m : nat) : (term147 m) = (term148 m).
Proof. exact (MK_COMB (@lem5351802) (@lem5351801 m)). Qed.
Lemma lem5351804 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem5351805 (m : nat) (x : nat) : (term141 m x) = (term149 m x).
Proof. exact (MK_COMB (@lem5351803 m) (@lem5351804 x)). Qed.
Lemma lem5351806 (m : nat) (x : nat) : (term89 m x) = (term149 m x).
Proof. exact (TRANS (@lem5351798 m x) (@lem5351805 m x)). Qed.
Lemma lem5351807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5351808 (m : nat) (x : nat) : (term150 m x) = (term151 m x).
Proof. exact (MK_COMB (@lem5351807) (@lem5351806 m x)). Qed.
Lemma lem5351810 (m : nat) (n : nat) : (Peano.le m n) = (term137 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5351811 (x : nat) (n : nat) : (Peano.le x n) = (term137 x n).
Proof. exact (@lem5351810 x n). Qed.
Lemma lem5351812 (m : nat) (x : nat) (n : nat) : (term36 m x n) = (term152 m x n).
Proof. exact (MK_COMB (@lem5351808 m x) (@lem5351811 x n)). Qed.
Lemma lem5351813 (m : nat) (x : nat) (n : nat) : (term51 m x n) = (term153 m x n).
Proof. exact (MK_COMB (@lem5351795 x m) (@lem5351812 m x n)). Qed.
Lemma lem5351814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5351815 (m : nat) (x : nat) (n : nat) : (term100 m x n) = (term154 m x n).
Proof. exact (MK_COMB (@lem5351814) (@lem5351813 m x n)). Qed.
Lemma lem5351817 (m : nat) (n : nat) : (Peano.le m n) = (term137 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5351818 (m : nat) (x : nat) : (Peano.le m x) = (term137 m x).
Proof. exact (@lem5351817 m x). Qed.
Lemma lem5351819 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5351820 (m : nat) (x : nat) : (term122 m x) = (term138 m x).
Proof. exact (MK_COMB (@lem5351819) (@lem5351818 m x)). Qed.
Lemma lem5351821 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5351822 (m : nat) (x : nat) : (term109 m x) = (term139 m x).
Proof. exact (MK_COMB (@lem5351821) (@lem5351820 m x)). Qed.
Lemma lem5351824 (m : nat) (n : nat) : (Peano.le m n) = (term137 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5351825 (x : nat) (n : nat) : (Peano.le x n) = (term137 x n).
Proof. exact (@lem5351824 x n). Qed.
Lemma lem5351826 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5351827 (x : nat) (n : nat) : (term122 x n) = (term138 x n).
Proof. exact (MK_COMB (@lem5351826) (@lem5351825 x n)). Qed.
Lemma lem5351828 (m : nat) (x : nat) (n : nat) : (term95 m x n) = (term155 m x n).
Proof. exact (MK_COMB (@lem5351822 m x) (@lem5351827 x n)). Qed.
Lemma lem5351829 (m : nat) (x : nat) (n : nat) : (term102 m x n) = (term156 m x n).
Proof. exact (MK_COMB (@lem5351815 m x n) (@lem5351828 m x n)). Qed.
Lemma lem5351830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5351831 (m : nat) (x : nat) (n : nat) : (term104 m x n) = (term157 m x n).
Proof. exact (MK_COMB (@lem5351830) (@lem5351829 m x n)). Qed.
Lemma lem5351833 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5351834 (x : nat) (m : nat) : (x = m) = ((int_of_num x) = (int_of_num m)).
Proof. exact (@lem5351833 x m). Qed.
Lemma lem5351837 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5351838 (x : nat) (m : nat) : (term158 x m) = (term159 x m).
Proof. exact (MK_COMB (@lem5351837) (@lem5351834 x m)). Qed.
Lemma lem5351839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5351840 (x : nat) (m : nat) : (term90 x m) = (term160 x m).
Proof. exact (MK_COMB (@lem5351839) (@lem5351838 x m)). Qed.
Lemma lem5351842 (m : nat) (n : nat) : (Peano.le m n) = (term137 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5351843 (m : nat) (x : nat) : (term89 m x) = (term141 m x).
Proof. exact (@lem5351842 (term29 m) x). Qed.
Lemma lem5351845 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5351846 (m : nat) : (term144 m) = (term145 m).
Proof. exact (@lem5351845 m term146). Qed.
Lemma lem5351847 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem5351848 (m : nat) : (term147 m) = (term148 m).
Proof. exact (MK_COMB (@lem5351847) (@lem5351846 m)). Qed.
Lemma lem5351849 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem5351850 (m : nat) (x : nat) : (term141 m x) = (term149 m x).
Proof. exact (MK_COMB (@lem5351848 m) (@lem5351849 x)). Qed.
Lemma lem5351851 (m : nat) (x : nat) : (term89 m x) = (term149 m x).
Proof. exact (TRANS (@lem5351843 m x) (@lem5351850 m x)). Qed.
Lemma lem5351852 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5351853 (m : nat) (x : nat) : (term161 m x) = (term162 m x).
Proof. exact (MK_COMB (@lem5351852) (@lem5351851 m x)). Qed.
Lemma lem5351854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5351855 (m : nat) (x : nat) : (term163 m x) = (term164 m x).
Proof. exact (MK_COMB (@lem5351854) (@lem5351853 m x)). Qed.
Lemma lem5351857 (m : nat) (n : nat) : (Peano.le m n) = (term137 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5351858 (x : nat) (n : nat) : (Peano.le x n) = (term137 x n).
Proof. exact (@lem5351857 x n). Qed.
Lemma lem5351859 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5351860 (x : nat) (n : nat) : (term122 x n) = (term138 x n).
Proof. exact (MK_COMB (@lem5351859) (@lem5351858 x n)). Qed.
Lemma lem5351861 (m : nat) (x : nat) (n : nat) : (term88 m x n) = (term165 m x n).
Proof. exact (MK_COMB (@lem5351855 m x) (@lem5351860 x n)). Qed.
Lemma lem5351862 (m : nat) (x : nat) (n : nat) : (term92 m x n) = (term166 m x n).
Proof. exact (MK_COMB (@lem5351840 x m) (@lem5351861 m x n)). Qed.
Lemma lem5351863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5351864 (m : nat) (x : nat) (n : nat) : (term97 m x n) = (term167 m x n).
Proof. exact (MK_COMB (@lem5351863) (@lem5351862 m x n)). Qed.
Lemma lem5351866 (m : nat) (n : nat) : (Peano.le m n) = (term137 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5351867 (m : nat) (x : nat) : (Peano.le m x) = (term137 m x).
Proof. exact (@lem5351866 m x). Qed.
Lemma lem5351868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5351869 (m : nat) (x : nat) : (term168 m x) = (term169 m x).
Proof. exact (MK_COMB (@lem5351868) (@lem5351867 m x)). Qed.
Lemma lem5351871 (m : nat) (n : nat) : (Peano.le m n) = (term137 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5351872 (x : nat) (n : nat) : (Peano.le x n) = (term137 x n).
Proof. exact (@lem5351871 x n). Qed.
Lemma lem5351873 (m : nat) (x : nat) (n : nat) : (term59 m x n) = (term170 m x n).
Proof. exact (MK_COMB (@lem5351869 m x) (@lem5351872 x n)). Qed.
Lemma lem5351874 (m : nat) (x : nat) (n : nat) : (term99 m x n) = (term171 m x n).
Proof. exact (MK_COMB (@lem5351864 m x n) (@lem5351873 m x n)). Qed.
Lemma lem5351875 (m : nat) (x : nat) (n : nat) : (term106 m x n) = (term172 m x n).
Proof. exact (MK_COMB (@lem5351831 m x n) (@lem5351874 m x n)). Qed.
Lemma lem5351876 (m : nat) (x : nat) (n : nat) : (term129 m x n) = (term173 m x n).
Proof. exact (MK_COMB (@lem5351788 m n) (@lem5351875 m x n)). Qed.
Lemma lem5351877 (m : nat) (n : nat) : (term131 m n) = (term174 m n).
Proof. exact (fun_ext (fun x : nat => @lem5351876 m x n)). Qed.
Lemma lem5351878 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351879 (m : nat) (n : nat) : (term132 m n) = (term175 m n).
Proof. exact (MK_COMB (@lem5351878) (@lem5351877 m n)). Qed.
Lemma lem5351880 (m : nat) : (term133 m) = (term176 m).
Proof. exact (fun_ext (fun n : nat => @lem5351879 m n)). Qed.
Lemma lem5351881 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351882 (m : nat) : (term134 m) = (term177 m).
Proof. exact (MK_COMB (@lem5351881) (@lem5351880 m)). Qed.
Lemma lem5351883 : term135 = term178.
Proof. exact (fun_ext (fun m : nat => @lem5351882 m)). Qed.
Lemma lem5351884 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5351885 : term136 = term179.
Proof. exact (MK_COMB (@lem5351884) (@lem5351883)). Qed.
Lemma lem5351886 : term86 = term179.
Proof. exact (TRANS (@lem5351782) (@lem5351885)). Qed.
Lemma lem5351887 (m : nat) : term180 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5351888 (m : nat) : (term180 m) = (term181 m).
Proof. exact (eq_refl (term180 m)). Qed.
Lemma lem5351889 (m : nat) : term181 m.
Proof. exact (EQ_MP (@lem5351888 m) (@lem5351887 m)). Qed.
Lemma lem5351890 (n : nat) : term180 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5351891 (n : nat) : (term180 n) = (term181 n).
Proof. exact (eq_refl (term180 n)). Qed.
Lemma lem5351892 (n : nat) : term181 n.
Proof. exact (EQ_MP (@lem5351891 n) (@lem5351890 n)). Qed.
Lemma lem5351893 (x : nat) : term180 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5351894 (x : nat) : (term180 x) = (term181 x).
Proof. exact (eq_refl (term180 x)). Qed.
Lemma lem5351895 (x : nat) : term181 x.
Proof. exact (EQ_MP (@lem5351894 x) (@lem5351893 x)). Qed.
Lemma lem5351896 (_69724 : int) (_69726 : int) (_69725 : int) : (term182 _69724 _69726 _69725) = (term183 _69724 _69726 _69725).
Proof. exact (@lem2318604 (term183 _69724 _69726 _69725)). Qed.
Lemma lem5351933 (_69724 : int) (_69725 : int) : (term184 _69724 _69725) = (int_le _69724 _69725).
Proof. exact (@lem16933 (int_le _69724 _69725)). Qed.
Lemma lem5351941 (_69724 : int) (_69726 : int) (_69725 : int) : (term185 _69724 _69726 _69725) = (term186 _69724 _69726 _69725).
Proof. exact (@lem17045 (term187 _69724 _69726) (int_le _69726 _69725)). Qed.
Lemma lem5351943 (_69726 : int) (_69724 : int) : (term188 _69726 _69724) = (term188 _69726 _69724).
Proof. exact (eq_refl (term188 _69726 _69724)). Qed.
Lemma lem5351944 (_69724 : int) (_69726 : int) (_69725 : int) : (term189 _69724 _69726 _69725) = (term190 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5351943 _69726 _69724) (@lem5351941 _69724 _69726 _69725)). Qed.
Lemma lem5351945 (_69724 : int) (_69726 : int) (_69725 : int) : (term191 _69724 _69726 _69725) = (term189 _69724 _69726 _69725).
Proof. exact (@lem17160 (_69726 = _69724) (term192 _69724 _69726 _69725)). Qed.
Lemma lem5351946 (_69724 : int) (_69726 : int) (_69725 : int) : (term191 _69724 _69726 _69725) = (term190 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5351945 _69724 _69726 _69725) (@lem5351944 _69724 _69726 _69725)). Qed.
Lemma lem5351949 (_69724 : int) (_69726 : int) : (term184 _69724 _69726) = (int_le _69724 _69726).
Proof. exact (@lem16933 (int_le _69724 _69726)). Qed.
Lemma lem5351952 (_69726 : int) (_69725 : int) : (term184 _69726 _69725) = (int_le _69726 _69725).
Proof. exact (@lem16933 (int_le _69726 _69725)). Qed.
Lemma lem5351953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5351954 (_69724 : int) (_69726 : int) : (term193 _69724 _69726) = (term194 _69724 _69726).
Proof. exact (MK_COMB (@lem5351953) (@lem5351949 _69724 _69726)). Qed.
Lemma lem5351955 (_69724 : int) (_69726 : int) (_69725 : int) : (term195 _69724 _69726 _69725) = (term196 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5351954 _69724 _69726) (@lem5351952 _69726 _69725)). Qed.
Lemma lem5351956 (_69724 : int) (_69726 : int) (_69725 : int) : (term197 _69724 _69726 _69725) = (term195 _69724 _69726 _69725).
Proof. exact (@lem17160 (term198 _69724 _69726) (term198 _69726 _69725)). Qed.
Lemma lem5351957 (_69724 : int) (_69726 : int) (_69725 : int) : (term197 _69724 _69726 _69725) = (term196 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5351956 _69724 _69726 _69725) (@lem5351955 _69724 _69726 _69725)). Qed.
Lemma lem5351958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5351959 (_69724 : int) (_69726 : int) (_69725 : int) : (term199 _69724 _69726 _69725) = (term200 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5351958) (@lem5351946 _69724 _69726 _69725)). Qed.
Lemma lem5351960 (_69724 : int) (_69726 : int) (_69725 : int) : (term201 _69724 _69726 _69725) = (term202 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5351959 _69724 _69726 _69725) (@lem5351957 _69724 _69726 _69725)). Qed.
Lemma lem5351961 (_69724 : int) (_69726 : int) (_69725 : int) : (term203 _69724 _69726 _69725) = (term201 _69724 _69726 _69725).
Proof. exact (@lem17160 (term204 _69724 _69726 _69725) (term205 _69724 _69726 _69725)). Qed.
Lemma lem5351962 (_69724 : int) (_69726 : int) (_69725 : int) : (term203 _69724 _69726 _69725) = (term202 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5351961 _69724 _69726 _69725) (@lem5351960 _69724 _69726 _69725)). Qed.
Lemma lem5351965 (_69726 : int) (_69724 : int) : (term206 _69726 _69724) = (_69726 = _69724).
Proof. exact (@lem16933 (_69726 = _69724)). Qed.
Lemma lem5351968 (_69724 : int) (_69726 : int) : (term207 _69724 _69726) = (term187 _69724 _69726).
Proof. exact (@lem16933 (term187 _69724 _69726)). Qed.
Lemma lem5351971 (_69726 : int) (_69725 : int) : (term184 _69726 _69725) = (int_le _69726 _69725).
Proof. exact (@lem16933 (int_le _69726 _69725)). Qed.
Lemma lem5351972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5351973 (_69724 : int) (_69726 : int) : (term208 _69724 _69726) = (term209 _69724 _69726).
Proof. exact (MK_COMB (@lem5351972) (@lem5351968 _69724 _69726)). Qed.
Lemma lem5351974 (_69724 : int) (_69726 : int) (_69725 : int) : (term210 _69724 _69726 _69725) = (term192 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5351973 _69724 _69726) (@lem5351971 _69726 _69725)). Qed.
Lemma lem5351975 (_69724 : int) (_69726 : int) (_69725 : int) : (term211 _69724 _69726 _69725) = (term210 _69724 _69726 _69725).
Proof. exact (@lem17160 (term212 _69724 _69726) (term198 _69726 _69725)). Qed.
Lemma lem5351976 (_69724 : int) (_69726 : int) (_69725 : int) : (term211 _69724 _69726 _69725) = (term192 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5351975 _69724 _69726 _69725) (@lem5351974 _69724 _69726 _69725)). Qed.
Lemma lem5351977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5351978 (_69726 : int) (_69724 : int) : (term213 _69726 _69724) = (term214 _69726 _69724).
Proof. exact (MK_COMB (@lem5351977) (@lem5351965 _69726 _69724)). Qed.
Lemma lem5351979 (_69724 : int) (_69726 : int) (_69725 : int) : (term215 _69724 _69726 _69725) = (term204 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5351978 _69726 _69724) (@lem5351976 _69724 _69726 _69725)). Qed.
Lemma lem5351980 (_69724 : int) (_69726 : int) (_69725 : int) : (term216 _69724 _69726 _69725) = (term215 _69724 _69726 _69725).
Proof. exact (@lem17045 (term217 _69726 _69724) (term186 _69724 _69726 _69725)). Qed.
Lemma lem5351981 (_69724 : int) (_69726 : int) (_69725 : int) : (term216 _69724 _69726 _69725) = (term204 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5351980 _69724 _69726 _69725) (@lem5351979 _69724 _69726 _69725)). Qed.
Lemma lem5351988 (_69724 : int) (_69726 : int) (_69725 : int) : (term218 _69724 _69726 _69725) = (term205 _69724 _69726 _69725).
Proof. exact (@lem17045 (int_le _69724 _69726) (int_le _69726 _69725)). Qed.
Lemma lem5351989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5351990 (_69724 : int) (_69726 : int) (_69725 : int) : (term219 _69724 _69726 _69725) = (term220 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5351989) (@lem5351981 _69724 _69726 _69725)). Qed.
Lemma lem5351991 (_69724 : int) (_69726 : int) (_69725 : int) : (term221 _69724 _69726 _69725) = (term222 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5351990 _69724 _69726 _69725) (@lem5351988 _69724 _69726 _69725)). Qed.
Lemma lem5351992 (_69724 : int) (_69726 : int) (_69725 : int) : (term223 _69724 _69726 _69725) = (term221 _69724 _69726 _69725).
Proof. exact (@lem17160 (term190 _69724 _69726 _69725) (term196 _69724 _69726 _69725)). Qed.
Lemma lem5351993 (_69724 : int) (_69726 : int) (_69725 : int) : (term223 _69724 _69726 _69725) = (term222 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5351992 _69724 _69726 _69725) (@lem5351991 _69724 _69726 _69725)). Qed.
Lemma lem5351994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5351995 (_69724 : int) (_69726 : int) (_69725 : int) : (term224 _69724 _69726 _69725) = (term225 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5351994) (@lem5351962 _69724 _69726 _69725)). Qed.
Lemma lem5351996 (_69724 : int) (_69726 : int) (_69725 : int) : (term226 _69724 _69726 _69725) = (term227 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5351995 _69724 _69726 _69725) (@lem5351993 _69724 _69726 _69725)). Qed.
Lemma lem5351997 (_69724 : int) (_69726 : int) (_69725 : int) : (term228 _69724 _69726 _69725) = (term226 _69724 _69726 _69725).
Proof. exact (@lem17045 (term229 _69724 _69726 _69725) (term230 _69724 _69726 _69725)). Qed.
Lemma lem5351998 (_69724 : int) (_69726 : int) (_69725 : int) : (term228 _69724 _69726 _69725) = (term227 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5351997 _69724 _69726 _69725) (@lem5351996 _69724 _69726 _69725)). Qed.
Lemma lem5351999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5352000 (_69724 : int) (_69725 : int) : (term193 _69724 _69725) = (term194 _69724 _69725).
Proof. exact (MK_COMB (@lem5351999) (@lem5351933 _69724 _69725)). Qed.
Lemma lem5352001 (_69724 : int) (_69726 : int) (_69725 : int) : (term231 _69724 _69726 _69725) = (term232 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5352000 _69724 _69725) (@lem5351998 _69724 _69726 _69725)). Qed.
Lemma lem5352002 (_69724 : int) (_69726 : int) (_69725 : int) : (term233 _69724 _69726 _69725) = (term231 _69724 _69726 _69725).
Proof. exact (@lem17160 (term198 _69724 _69725) (term234 _69724 _69726 _69725)). Qed.
Lemma lem5352003 (_69724 : int) (_69726 : int) (_69725 : int) : (term233 _69724 _69726 _69725) = (term232 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5352002 _69724 _69726 _69725) (@lem5352001 _69724 _69726 _69725)). Qed.
Lemma lem5352005 (_69726 : int) : (term235 _69726) = (term235 _69726).
Proof. exact (eq_refl (term235 _69726)). Qed.
Lemma lem5352006 (_69724 : int) (_69726 : int) (_69725 : int) : (term236 _69724 _69726 _69725) = (term237 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5352005 _69726) (@lem5352003 _69724 _69726 _69725)). Qed.
Lemma lem5352007 (_69724 : int) (_69726 : int) (_69725 : int) : (term238 _69724 _69726 _69725) = (term236 _69724 _69726 _69725).
Proof. exact (@lem17362 (term239 _69726) (term240 _69724 _69726 _69725)). Qed.
Lemma lem5352008 (_69724 : int) (_69726 : int) (_69725 : int) : (term238 _69724 _69726 _69725) = (term237 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5352007 _69724 _69726 _69725) (@lem5352006 _69724 _69726 _69725)). Qed.
Lemma lem5352010 (_69725 : int) : (term235 _69725) = (term235 _69725).
Proof. exact (eq_refl (term235 _69725)). Qed.
Lemma lem5352011 (_69724 : int) (_69726 : int) (_69725 : int) : (term241 _69724 _69726 _69725) = (term242 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5352010 _69725) (@lem5352008 _69724 _69726 _69725)). Qed.
Lemma lem5352012 (_69724 : int) (_69726 : int) (_69725 : int) : (term243 _69724 _69726 _69725) = (term241 _69724 _69726 _69725).
Proof. exact (@lem17362 (term239 _69725) (term244 _69724 _69726 _69725)). Qed.
Lemma lem5352013 (_69724 : int) (_69726 : int) (_69725 : int) : (term243 _69724 _69726 _69725) = (term242 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5352012 _69724 _69726 _69725) (@lem5352011 _69724 _69726 _69725)). Qed.
Lemma lem5352015 (_69724 : int) : (term235 _69724) = (term235 _69724).
Proof. exact (eq_refl (term235 _69724)). Qed.
Lemma lem5352016 (_69724 : int) (_69726 : int) (_69725 : int) : (term245 _69724 _69726 _69725) = (term246 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5352015 _69724) (@lem5352013 _69724 _69726 _69725)). Qed.
Lemma lem5352017 (_69724 : int) (_69726 : int) (_69725 : int) : (term247 _69724 _69726 _69725) = (term245 _69724 _69726 _69725).
Proof. exact (@lem17362 (term239 _69724) (term248 _69724 _69726 _69725)). Qed.
Lemma lem5352083 (_69724 : int) (_69726 : int) (_69725 : int) : (term247 _69724 _69726 _69725) = (term246 _69724 _69726 _69725).
Proof. exact (TRANS (@lem5352017 _69724 _69726 _69725) (@lem5352016 _69724 _69726 _69725)). Qed.
Lemma lem5352086 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352087 (_69724 : int) : (term239 _69724) = (term250 _69724).
Proof. exact (@lem5352086 term251 _69724). Qed.
Lemma lem5352089 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352090 : term253 = term254.
Proof. exact (@lem5352089 (NUMERAL 0)). Qed.
Lemma lem5352091 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5352092 : term255 = term256.
Proof. exact (MK_COMB (@lem5352091) (@lem5352090)). Qed.
Lemma lem5352093 (_69724 : int) : (real_of_int _69724) = (real_of_int _69724).
Proof. exact (eq_refl (real_of_int _69724)). Qed.
Lemma lem5352094 (_69724 : int) : (term250 _69724) = (term257 _69724).
Proof. exact (MK_COMB (@lem5352092) (@lem5352093 _69724)). Qed.
Lemma lem5352096 (_69724 : int) : (term239 _69724) = (term257 _69724).
Proof. exact (TRANS (@lem5352087 _69724) (@lem5352094 _69724)). Qed.
Lemma lem5352099 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352100 (_69725 : int) : (term239 _69725) = (term250 _69725).
Proof. exact (@lem5352099 term251 _69725). Qed.
Lemma lem5352102 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352103 : term253 = term254.
Proof. exact (@lem5352102 (NUMERAL 0)). Qed.
Lemma lem5352104 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5352105 : term255 = term256.
Proof. exact (MK_COMB (@lem5352104) (@lem5352103)). Qed.
Lemma lem5352106 (_69725 : int) : (real_of_int _69725) = (real_of_int _69725).
Proof. exact (eq_refl (real_of_int _69725)). Qed.
Lemma lem5352107 (_69725 : int) : (term250 _69725) = (term257 _69725).
Proof. exact (MK_COMB (@lem5352105) (@lem5352106 _69725)). Qed.
Lemma lem5352109 (_69725 : int) : (term239 _69725) = (term257 _69725).
Proof. exact (TRANS (@lem5352100 _69725) (@lem5352107 _69725)). Qed.
Lemma lem5352112 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352113 (_69726 : int) : (term239 _69726) = (term250 _69726).
Proof. exact (@lem5352112 term251 _69726). Qed.
Lemma lem5352115 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352116 : term253 = term254.
Proof. exact (@lem5352115 (NUMERAL 0)). Qed.
Lemma lem5352117 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5352118 : term255 = term256.
Proof. exact (MK_COMB (@lem5352117) (@lem5352116)). Qed.
Lemma lem5352119 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5352120 (_69726 : int) : (term250 _69726) = (term257 _69726).
Proof. exact (MK_COMB (@lem5352118) (@lem5352119 _69726)). Qed.
Lemma lem5352122 (_69726 : int) : (term239 _69726) = (term257 _69726).
Proof. exact (TRANS (@lem5352113 _69726) (@lem5352120 _69726)). Qed.
Lemma lem5352125 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352127 (_69724 : int) (_69725 : int) : (int_le _69724 _69725) = (term249 _69724 _69725).
Proof. exact (@lem5352125 _69724 _69725). Qed.
Lemma lem5352129 (y : int) (x : int) : (term217 x y) = (term258 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem5352130 (_69724 : int) (_69726 : int) : (term217 _69726 _69724) = (term258 _69724 _69726).
Proof. exact (@lem5352129 _69724 _69726). Qed.
Lemma lem5352132 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352133 (_69726 : int) (_69724 : int) : (term187 _69726 _69724) = (term259 _69726 _69724).
Proof. exact (@lem5352132 (term260 _69726) _69724). Qed.
Lemma lem5352135 (x : int) (y : int) : (term261 x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5352136 (_69726 : int) : (term263 _69726) = (term264 _69726).
Proof. exact (@lem5352135 _69726 term265). Qed.
Lemma lem5352138 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352139 : term266 = term267.
Proof. exact (@lem5352138 term146). Qed.
Lemma lem5352140 (_69726 : int) : (term268 _69726) = (term268 _69726).
Proof. exact (eq_refl (term268 _69726)). Qed.
Lemma lem5352141 (_69726 : int) : (term264 _69726) = (term269 _69726).
Proof. exact (MK_COMB (@lem5352140 _69726) (@lem5352139)). Qed.
Lemma lem5352142 (_69726 : int) : (term263 _69726) = (term269 _69726).
Proof. exact (TRANS (@lem5352136 _69726) (@lem5352141 _69726)). Qed.
Lemma lem5352143 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5352144 (_69726 : int) : (term270 _69726) = (term271 _69726).
Proof. exact (MK_COMB (@lem5352143) (@lem5352142 _69726)). Qed.
Lemma lem5352145 (_69724 : int) : (real_of_int _69724) = (real_of_int _69724).
Proof. exact (eq_refl (real_of_int _69724)). Qed.
Lemma lem5352146 (_69726 : int) (_69724 : int) : (term259 _69726 _69724) = (term272 _69726 _69724).
Proof. exact (MK_COMB (@lem5352144 _69726) (@lem5352145 _69724)). Qed.
Lemma lem5352147 (_69726 : int) (_69724 : int) : (term187 _69726 _69724) = (term272 _69726 _69724).
Proof. exact (TRANS (@lem5352133 _69726 _69724) (@lem5352146 _69726 _69724)). Qed.
Lemma lem5352148 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5352149 (_69726 : int) (_69724 : int) : (term273 _69726 _69724) = (term274 _69726 _69724).
Proof. exact (MK_COMB (@lem5352148) (@lem5352147 _69726 _69724)). Qed.
Lemma lem5352151 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352152 (_69724 : int) (_69726 : int) : (term187 _69724 _69726) = (term259 _69724 _69726).
Proof. exact (@lem5352151 (term260 _69724) _69726). Qed.
Lemma lem5352154 (x : int) (y : int) : (term261 x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5352155 (_69724 : int) : (term263 _69724) = (term264 _69724).
Proof. exact (@lem5352154 _69724 term265). Qed.
Lemma lem5352157 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352158 : term266 = term267.
Proof. exact (@lem5352157 term146). Qed.
Lemma lem5352159 (_69724 : int) : (term268 _69724) = (term268 _69724).
Proof. exact (eq_refl (term268 _69724)). Qed.
Lemma lem5352160 (_69724 : int) : (term264 _69724) = (term269 _69724).
Proof. exact (MK_COMB (@lem5352159 _69724) (@lem5352158)). Qed.
Lemma lem5352161 (_69724 : int) : (term263 _69724) = (term269 _69724).
Proof. exact (TRANS (@lem5352155 _69724) (@lem5352160 _69724)). Qed.
Lemma lem5352162 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5352163 (_69724 : int) : (term270 _69724) = (term271 _69724).
Proof. exact (MK_COMB (@lem5352162) (@lem5352161 _69724)). Qed.
Lemma lem5352164 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5352165 (_69724 : int) (_69726 : int) : (term259 _69724 _69726) = (term272 _69724 _69726).
Proof. exact (MK_COMB (@lem5352163 _69724) (@lem5352164 _69726)). Qed.
Lemma lem5352166 (_69724 : int) (_69726 : int) : (term187 _69724 _69726) = (term272 _69724 _69726).
Proof. exact (TRANS (@lem5352152 _69724 _69726) (@lem5352165 _69724 _69726)). Qed.
Lemma lem5352167 (_69724 : int) (_69726 : int) : (term258 _69724 _69726) = (term275 _69724 _69726).
Proof. exact (MK_COMB (@lem5352149 _69726 _69724) (@lem5352166 _69724 _69726)). Qed.
Lemma lem5352168 (_69724 : int) (_69726 : int) : (term217 _69726 _69724) = (term275 _69724 _69726).
Proof. exact (TRANS (@lem5352130 _69724 _69726) (@lem5352167 _69724 _69726)). Qed.
Lemma lem5352170 (y : int) (x : int) : (term198 x y) = (term187 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5352171 (_69726 : int) (_69724 : int) : (term212 _69724 _69726) = (term276 _69726 _69724).
Proof. exact (@lem5352170 _69726 (term260 _69724)). Qed.
Lemma lem5352173 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352174 (_69726 : int) (_69724 : int) : (term276 _69726 _69724) = (term277 _69726 _69724).
Proof. exact (@lem5352173 (term260 _69726) (term260 _69724)). Qed.
Lemma lem5352176 (x : int) (y : int) : (term261 x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5352177 (_69726 : int) : (term263 _69726) = (term264 _69726).
Proof. exact (@lem5352176 _69726 term265). Qed.
Lemma lem5352179 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352180 : term266 = term267.
Proof. exact (@lem5352179 term146). Qed.
Lemma lem5352181 (_69726 : int) : (term268 _69726) = (term268 _69726).
Proof. exact (eq_refl (term268 _69726)). Qed.
Lemma lem5352182 (_69726 : int) : (term264 _69726) = (term269 _69726).
Proof. exact (MK_COMB (@lem5352181 _69726) (@lem5352180)). Qed.
Lemma lem5352183 (_69726 : int) : (term263 _69726) = (term269 _69726).
Proof. exact (TRANS (@lem5352177 _69726) (@lem5352182 _69726)). Qed.
Lemma lem5352184 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5352185 (_69726 : int) : (term270 _69726) = (term271 _69726).
Proof. exact (MK_COMB (@lem5352184) (@lem5352183 _69726)). Qed.
Lemma lem5352187 (x : int) (y : int) : (term261 x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5352188 (_69724 : int) : (term263 _69724) = (term264 _69724).
Proof. exact (@lem5352187 _69724 term265). Qed.
Lemma lem5352190 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352191 : term266 = term267.
Proof. exact (@lem5352190 term146). Qed.
Lemma lem5352192 (_69724 : int) : (term268 _69724) = (term268 _69724).
Proof. exact (eq_refl (term268 _69724)). Qed.
Lemma lem5352193 (_69724 : int) : (term264 _69724) = (term269 _69724).
Proof. exact (MK_COMB (@lem5352192 _69724) (@lem5352191)). Qed.
Lemma lem5352194 (_69724 : int) : (term263 _69724) = (term269 _69724).
Proof. exact (TRANS (@lem5352188 _69724) (@lem5352193 _69724)). Qed.
Lemma lem5352195 (_69726 : int) (_69724 : int) : (term277 _69726 _69724) = (term278 _69726 _69724).
Proof. exact (MK_COMB (@lem5352185 _69726) (@lem5352194 _69724)). Qed.
Lemma lem5352196 (_69726 : int) (_69724 : int) : (term276 _69726 _69724) = (term278 _69726 _69724).
Proof. exact (TRANS (@lem5352174 _69726 _69724) (@lem5352195 _69726 _69724)). Qed.
Lemma lem5352197 (_69726 : int) (_69724 : int) : (term212 _69724 _69726) = (term278 _69726 _69724).
Proof. exact (TRANS (@lem5352171 _69726 _69724) (@lem5352196 _69726 _69724)). Qed.
Lemma lem5352199 (y : int) (x : int) : (term198 x y) = (term187 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5352200 (_69725 : int) (_69726 : int) : (term198 _69726 _69725) = (term187 _69725 _69726).
Proof. exact (@lem5352199 _69725 _69726). Qed.
Lemma lem5352202 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352203 (_69725 : int) (_69726 : int) : (term187 _69725 _69726) = (term259 _69725 _69726).
Proof. exact (@lem5352202 (term260 _69725) _69726). Qed.
Lemma lem5352205 (x : int) (y : int) : (term261 x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5352206 (_69725 : int) : (term263 _69725) = (term264 _69725).
Proof. exact (@lem5352205 _69725 term265). Qed.
Lemma lem5352208 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352209 : term266 = term267.
Proof. exact (@lem5352208 term146). Qed.
Lemma lem5352210 (_69725 : int) : (term268 _69725) = (term268 _69725).
Proof. exact (eq_refl (term268 _69725)). Qed.
Lemma lem5352211 (_69725 : int) : (term264 _69725) = (term269 _69725).
Proof. exact (MK_COMB (@lem5352210 _69725) (@lem5352209)). Qed.
Lemma lem5352212 (_69725 : int) : (term263 _69725) = (term269 _69725).
Proof. exact (TRANS (@lem5352206 _69725) (@lem5352211 _69725)). Qed.
Lemma lem5352213 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5352214 (_69725 : int) : (term270 _69725) = (term271 _69725).
Proof. exact (MK_COMB (@lem5352213) (@lem5352212 _69725)). Qed.
Lemma lem5352215 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5352216 (_69725 : int) (_69726 : int) : (term259 _69725 _69726) = (term272 _69725 _69726).
Proof. exact (MK_COMB (@lem5352214 _69725) (@lem5352215 _69726)). Qed.
Lemma lem5352217 (_69725 : int) (_69726 : int) : (term187 _69725 _69726) = (term272 _69725 _69726).
Proof. exact (TRANS (@lem5352203 _69725 _69726) (@lem5352216 _69725 _69726)). Qed.
Lemma lem5352218 (_69725 : int) (_69726 : int) : (term198 _69726 _69725) = (term272 _69725 _69726).
Proof. exact (TRANS (@lem5352200 _69725 _69726) (@lem5352217 _69725 _69726)). Qed.
Lemma lem5352219 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5352220 (_69726 : int) (_69724 : int) : (term279 _69724 _69726) = (term280 _69726 _69724).
Proof. exact (MK_COMB (@lem5352219) (@lem5352197 _69726 _69724)). Qed.
Lemma lem5352221 (_69724 : int) (_69725 : int) (_69726 : int) : (term186 _69724 _69726 _69725) = (term281 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5352220 _69726 _69724) (@lem5352218 _69725 _69726)). Qed.
Lemma lem5352222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5352223 (_69724 : int) (_69726 : int) : (term188 _69726 _69724) = (term282 _69724 _69726).
Proof. exact (MK_COMB (@lem5352222) (@lem5352168 _69724 _69726)). Qed.
Lemma lem5352224 (_69724 : int) (_69725 : int) (_69726 : int) : (term190 _69724 _69726 _69725) = (term283 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5352223 _69724 _69726) (@lem5352221 _69724 _69725 _69726)). Qed.
Lemma lem5352227 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352229 (_69724 : int) (_69726 : int) : (int_le _69724 _69726) = (term249 _69724 _69726).
Proof. exact (@lem5352227 _69724 _69726). Qed.
Lemma lem5352232 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352234 (_69726 : int) (_69725 : int) : (int_le _69726 _69725) = (term249 _69726 _69725).
Proof. exact (@lem5352232 _69726 _69725). Qed.
Lemma lem5352235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5352236 (_69724 : int) (_69726 : int) : (term194 _69724 _69726) = (term284 _69724 _69726).
Proof. exact (MK_COMB (@lem5352235) (@lem5352229 _69724 _69726)). Qed.
Lemma lem5352237 (_69724 : int) (_69726 : int) (_69725 : int) : (term196 _69724 _69726 _69725) = (term285 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5352236 _69724 _69726) (@lem5352234 _69726 _69725)). Qed.
Lemma lem5352238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5352239 (_69724 : int) (_69725 : int) (_69726 : int) : (term200 _69724 _69726 _69725) = (term286 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5352238) (@lem5352224 _69724 _69725 _69726)). Qed.
Lemma lem5352240 (_69724 : int) (_69726 : int) (_69725 : int) : (term202 _69724 _69726 _69725) = (term287 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5352239 _69724 _69725 _69726) (@lem5352237 _69724 _69726 _69725)). Qed.
Lemma lem5352243 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5352247 (_69726 : int) (_69724 : int) : (_69726 = _69724) = ((real_of_int _69726) = (real_of_int _69724)).
Proof. exact (@lem5352243 _69726 _69724). Qed.
Lemma lem5352250 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352251 (_69724 : int) (_69726 : int) : (term187 _69724 _69726) = (term259 _69724 _69726).
Proof. exact (@lem5352250 (term260 _69724) _69726). Qed.
Lemma lem5352253 (x : int) (y : int) : (term261 x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5352254 (_69724 : int) : (term263 _69724) = (term264 _69724).
Proof. exact (@lem5352253 _69724 term265). Qed.
Lemma lem5352256 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352257 : term266 = term267.
Proof. exact (@lem5352256 term146). Qed.
Lemma lem5352258 (_69724 : int) : (term268 _69724) = (term268 _69724).
Proof. exact (eq_refl (term268 _69724)). Qed.
Lemma lem5352259 (_69724 : int) : (term264 _69724) = (term269 _69724).
Proof. exact (MK_COMB (@lem5352258 _69724) (@lem5352257)). Qed.
Lemma lem5352260 (_69724 : int) : (term263 _69724) = (term269 _69724).
Proof. exact (TRANS (@lem5352254 _69724) (@lem5352259 _69724)). Qed.
Lemma lem5352261 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5352262 (_69724 : int) : (term270 _69724) = (term271 _69724).
Proof. exact (MK_COMB (@lem5352261) (@lem5352260 _69724)). Qed.
Lemma lem5352263 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5352264 (_69724 : int) (_69726 : int) : (term259 _69724 _69726) = (term272 _69724 _69726).
Proof. exact (MK_COMB (@lem5352262 _69724) (@lem5352263 _69726)). Qed.
Lemma lem5352266 (_69724 : int) (_69726 : int) : (term187 _69724 _69726) = (term272 _69724 _69726).
Proof. exact (TRANS (@lem5352251 _69724 _69726) (@lem5352264 _69724 _69726)). Qed.
Lemma lem5352269 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352271 (_69726 : int) (_69725 : int) : (int_le _69726 _69725) = (term249 _69726 _69725).
Proof. exact (@lem5352269 _69726 _69725). Qed.
Lemma lem5352272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5352273 (_69724 : int) (_69726 : int) : (term209 _69724 _69726) = (term288 _69724 _69726).
Proof. exact (MK_COMB (@lem5352272) (@lem5352266 _69724 _69726)). Qed.
Lemma lem5352274 (_69724 : int) (_69726 : int) (_69725 : int) : (term192 _69724 _69726 _69725) = (term289 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5352273 _69724 _69726) (@lem5352271 _69726 _69725)). Qed.
Lemma lem5352275 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5352276 (_69726 : int) (_69724 : int) : (term214 _69726 _69724) = (term290 _69726 _69724).
Proof. exact (MK_COMB (@lem5352275) (@lem5352247 _69726 _69724)). Qed.
Lemma lem5352277 (_69724 : int) (_69726 : int) (_69725 : int) : (term204 _69724 _69726 _69725) = (term291 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5352276 _69726 _69724) (@lem5352274 _69724 _69726 _69725)). Qed.
Lemma lem5352279 (y : int) (x : int) : (term198 x y) = (term187 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5352280 (_69726 : int) (_69724 : int) : (term198 _69724 _69726) = (term187 _69726 _69724).
Proof. exact (@lem5352279 _69726 _69724). Qed.
Lemma lem5352282 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352283 (_69726 : int) (_69724 : int) : (term187 _69726 _69724) = (term259 _69726 _69724).
Proof. exact (@lem5352282 (term260 _69726) _69724). Qed.
Lemma lem5352285 (x : int) (y : int) : (term261 x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5352286 (_69726 : int) : (term263 _69726) = (term264 _69726).
Proof. exact (@lem5352285 _69726 term265). Qed.
Lemma lem5352288 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352289 : term266 = term267.
Proof. exact (@lem5352288 term146). Qed.
Lemma lem5352290 (_69726 : int) : (term268 _69726) = (term268 _69726).
Proof. exact (eq_refl (term268 _69726)). Qed.
Lemma lem5352291 (_69726 : int) : (term264 _69726) = (term269 _69726).
Proof. exact (MK_COMB (@lem5352290 _69726) (@lem5352289)). Qed.
Lemma lem5352292 (_69726 : int) : (term263 _69726) = (term269 _69726).
Proof. exact (TRANS (@lem5352286 _69726) (@lem5352291 _69726)). Qed.
Lemma lem5352293 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5352294 (_69726 : int) : (term270 _69726) = (term271 _69726).
Proof. exact (MK_COMB (@lem5352293) (@lem5352292 _69726)). Qed.
Lemma lem5352295 (_69724 : int) : (real_of_int _69724) = (real_of_int _69724).
Proof. exact (eq_refl (real_of_int _69724)). Qed.
Lemma lem5352296 (_69726 : int) (_69724 : int) : (term259 _69726 _69724) = (term272 _69726 _69724).
Proof. exact (MK_COMB (@lem5352294 _69726) (@lem5352295 _69724)). Qed.
Lemma lem5352297 (_69726 : int) (_69724 : int) : (term187 _69726 _69724) = (term272 _69726 _69724).
Proof. exact (TRANS (@lem5352283 _69726 _69724) (@lem5352296 _69726 _69724)). Qed.
Lemma lem5352298 (_69726 : int) (_69724 : int) : (term198 _69724 _69726) = (term272 _69726 _69724).
Proof. exact (TRANS (@lem5352280 _69726 _69724) (@lem5352297 _69726 _69724)). Qed.
Lemma lem5352300 (y : int) (x : int) : (term198 x y) = (term187 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5352301 (_69725 : int) (_69726 : int) : (term198 _69726 _69725) = (term187 _69725 _69726).
Proof. exact (@lem5352300 _69725 _69726). Qed.
Lemma lem5352303 (x : int) (y : int) : (int_le x y) = (term249 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5352304 (_69725 : int) (_69726 : int) : (term187 _69725 _69726) = (term259 _69725 _69726).
Proof. exact (@lem5352303 (term260 _69725) _69726). Qed.
Lemma lem5352306 (x : int) (y : int) : (term261 x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5352307 (_69725 : int) : (term263 _69725) = (term264 _69725).
Proof. exact (@lem5352306 _69725 term265). Qed.
Lemma lem5352309 (n : nat) : (term252 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5352310 : term266 = term267.
Proof. exact (@lem5352309 term146). Qed.
Lemma lem5352311 (_69725 : int) : (term268 _69725) = (term268 _69725).
Proof. exact (eq_refl (term268 _69725)). Qed.
Lemma lem5352312 (_69725 : int) : (term264 _69725) = (term269 _69725).
Proof. exact (MK_COMB (@lem5352311 _69725) (@lem5352310)). Qed.
Lemma lem5352313 (_69725 : int) : (term263 _69725) = (term269 _69725).
Proof. exact (TRANS (@lem5352307 _69725) (@lem5352312 _69725)). Qed.
Lemma lem5352314 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5352315 (_69725 : int) : (term270 _69725) = (term271 _69725).
Proof. exact (MK_COMB (@lem5352314) (@lem5352313 _69725)). Qed.
Lemma lem5352316 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5352317 (_69725 : int) (_69726 : int) : (term259 _69725 _69726) = (term272 _69725 _69726).
Proof. exact (MK_COMB (@lem5352315 _69725) (@lem5352316 _69726)). Qed.
Lemma lem5352318 (_69725 : int) (_69726 : int) : (term187 _69725 _69726) = (term272 _69725 _69726).
Proof. exact (TRANS (@lem5352304 _69725 _69726) (@lem5352317 _69725 _69726)). Qed.
Lemma lem5352319 (_69725 : int) (_69726 : int) : (term198 _69726 _69725) = (term272 _69725 _69726).
Proof. exact (TRANS (@lem5352301 _69725 _69726) (@lem5352318 _69725 _69726)). Qed.
Lemma lem5352320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5352321 (_69726 : int) (_69724 : int) : (term292 _69724 _69726) = (term274 _69726 _69724).
Proof. exact (MK_COMB (@lem5352320) (@lem5352298 _69726 _69724)). Qed.
Lemma lem5352322 (_69724 : int) (_69725 : int) (_69726 : int) : (term205 _69724 _69726 _69725) = (term293 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5352321 _69726 _69724) (@lem5352319 _69725 _69726)). Qed.
Lemma lem5352323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5352324 (_69724 : int) (_69726 : int) (_69725 : int) : (term220 _69724 _69726 _69725) = (term294 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5352323) (@lem5352277 _69724 _69726 _69725)). Qed.
Lemma lem5352325 (_69724 : int) (_69725 : int) (_69726 : int) : (term222 _69724 _69726 _69725) = (term295 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5352324 _69724 _69726 _69725) (@lem5352322 _69724 _69725 _69726)). Qed.
Lemma lem5352326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5352327 (_69724 : int) (_69726 : int) (_69725 : int) : (term225 _69724 _69726 _69725) = (term296 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5352326) (@lem5352240 _69724 _69726 _69725)). Qed.
Lemma lem5352328 (_69724 : int) (_69725 : int) (_69726 : int) : (term227 _69724 _69726 _69725) = (term297 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5352327 _69724 _69726 _69725) (@lem5352325 _69724 _69725 _69726)). Qed.
Lemma lem5352329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5352330 (_69724 : int) (_69725 : int) : (term194 _69724 _69725) = (term284 _69724 _69725).
Proof. exact (MK_COMB (@lem5352329) (@lem5352127 _69724 _69725)). Qed.
Lemma lem5352331 (_69724 : int) (_69725 : int) (_69726 : int) : (term232 _69724 _69726 _69725) = (term298 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5352330 _69724 _69725) (@lem5352328 _69724 _69725 _69726)). Qed.
Lemma lem5352332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5352333 (_69726 : int) : (term235 _69726) = (term299 _69726).
Proof. exact (MK_COMB (@lem5352332) (@lem5352122 _69726)). Qed.
Lemma lem5352334 (_69724 : int) (_69725 : int) (_69726 : int) : (term237 _69724 _69726 _69725) = (term300 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5352333 _69726) (@lem5352331 _69724 _69725 _69726)). Qed.
Lemma lem5352335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5352336 (_69725 : int) : (term235 _69725) = (term299 _69725).
Proof. exact (MK_COMB (@lem5352335) (@lem5352109 _69725)). Qed.
Lemma lem5352337 (_69724 : int) (_69725 : int) (_69726 : int) : (term242 _69724 _69726 _69725) = (term301 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5352336 _69725) (@lem5352334 _69724 _69725 _69726)). Qed.
Lemma lem5352338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5352339 (_69724 : int) : (term235 _69724) = (term299 _69724).
Proof. exact (MK_COMB (@lem5352338) (@lem5352096 _69724)). Qed.
Lemma lem5352340 (_69724 : int) (_69725 : int) (_69726 : int) : (term246 _69724 _69726 _69725) = (term302 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5352339 _69724) (@lem5352337 _69724 _69725 _69726)). Qed.
Lemma lem5352341 (_69724 : int) (_69725 : int) (_69726 : int) : (term247 _69724 _69726 _69725) = (term302 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5352083 _69724 _69726 _69725) (@lem5352340 _69724 _69725 _69726)). Qed.
Lemma lem5352345 (t : Prop) : (term303 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5352491 (_69724 : int) (_69725 : int) (_69726 : int) : (term304 _69724 _69725 _69726) = (term302 _69724 _69725 _69726).
Proof. exact (@lem5352345 (term302 _69724 _69725 _69726)). Qed.
Lemma lem5352492 (_69724 : int) : (term257 _69724) = (term305 _69724).
Proof. exact (@lem1988287 (real_of_int _69724) term254). Qed.
Lemma lem5352498 (_69724 : int) : (term306 _69724) = (term307 _69724).
Proof. exact (@lem1982792 (real_of_int _69724) term254). Qed.
Lemma lem5352500 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5352501 : term254 = term309.
Proof. exact (@lem5352500 (NUMERAL 0)). Qed.
Lemma lem5352503 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5352504 : term312 = term313.
Proof. exact (@lem5352503 term146). Qed.
Lemma lem5352505 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5352506 : term314 = term315.
Proof. exact (MK_COMB (@lem5352505) (@lem5352504)). Qed.
Lemma lem5352507 : term316 = term317.
Proof. exact (MK_COMB (@lem5352506) (@lem5352501)). Qed.
Lemma lem5352508 : term317 = term318.
Proof. exact (@lem1981613 term312 term254 term267 term267). Qed.
Lemma lem5352510 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5352511 : term321 = term322.
Proof. exact (@lem5352510 term146 term146). Qed.
Lemma lem5352512 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352513 : term324 = term146.
Proof. exact (EQ_MP (@lem5352512) (@lem940073)). Qed.
Lemma lem5352514 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352515 : term322 = term267.
Proof. exact (MK_COMB (@lem5352514) (@lem5352513)). Qed.
Lemma lem5352516 : term321 = term267.
Proof. exact (TRANS (@lem5352511) (@lem5352515)). Qed.
Lemma lem5352518 (x : nat) : (term325 x) = term254.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5352519 : term316 = term254.
Proof. exact (@lem5352518 term146). Qed.
Lemma lem5352520 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5352521 : term326 = term327.
Proof. exact (MK_COMB (@lem5352520) (@lem5352519)). Qed.
Lemma lem5352522 : term318 = term309.
Proof. exact (MK_COMB (@lem5352521) (@lem5352516)). Qed.
Lemma lem5352523 : term317 = term309.
Proof. exact (TRANS (@lem5352508) (@lem5352522)). Qed.
Lemma lem5352524 : term316 = term309.
Proof. exact (TRANS (@lem5352507) (@lem5352523)). Qed.
Lemma lem5352526 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5352527 : term309 = term254.
Proof. exact (@lem5352526 term254). Qed.
Lemma lem5352528 : term316 = term254.
Proof. exact (TRANS (@lem5352524) (@lem5352527)). Qed.
Lemma lem5352529 (_69724 : int) : (term268 _69724) = (term268 _69724).
Proof. exact (eq_refl (term268 _69724)). Qed.
Lemma lem5352530 (_69724 : int) : (term307 _69724) = (term329 _69724).
Proof. exact (MK_COMB (@lem5352529 _69724) (@lem5352528)). Qed.
Lemma lem5352531 (_69724 : int) : (term329 _69724) = (real_of_int _69724).
Proof. exact (@lem1982723 (real_of_int _69724)). Qed.
Lemma lem5352532 (_69724 : int) : (term307 _69724) = (real_of_int _69724).
Proof. exact (TRANS (@lem5352530 _69724) (@lem5352531 _69724)). Qed.
Lemma lem5352534 (_69724 : int) : (term306 _69724) = (real_of_int _69724).
Proof. exact (TRANS (@lem5352498 _69724) (@lem5352532 _69724)). Qed.
Lemma lem5352535 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5352536 (_69724 : int) : (term330 _69724) = (term331 _69724).
Proof. exact (MK_COMB (@lem5352535) (@lem5352534 _69724)). Qed.
Lemma lem5352537 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5352538 (_69724 : int) : (term305 _69724) = (term332 _69724).
Proof. exact (MK_COMB (@lem5352536 _69724) (@lem5352537)). Qed.
Lemma lem5352539 (_69724 : int) : (term257 _69724) = (term332 _69724).
Proof. exact (TRANS (@lem5352492 _69724) (@lem5352538 _69724)). Qed.
Lemma lem5352540 (_69725 : int) : (term257 _69725) = (term305 _69725).
Proof. exact (@lem1988287 (real_of_int _69725) term254). Qed.
Lemma lem5352546 (_69725 : int) : (term306 _69725) = (term307 _69725).
Proof. exact (@lem1982792 (real_of_int _69725) term254). Qed.
Lemma lem5352548 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5352549 : term254 = term309.
Proof. exact (@lem5352548 (NUMERAL 0)). Qed.
Lemma lem5352551 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5352552 : term312 = term313.
Proof. exact (@lem5352551 term146). Qed.
Lemma lem5352553 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5352554 : term314 = term315.
Proof. exact (MK_COMB (@lem5352553) (@lem5352552)). Qed.
Lemma lem5352555 : term316 = term317.
Proof. exact (MK_COMB (@lem5352554) (@lem5352549)). Qed.
Lemma lem5352556 : term317 = term318.
Proof. exact (@lem1981613 term312 term254 term267 term267). Qed.
Lemma lem5352558 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5352559 : term321 = term322.
Proof. exact (@lem5352558 term146 term146). Qed.
Lemma lem5352560 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352561 : term324 = term146.
Proof. exact (EQ_MP (@lem5352560) (@lem940073)). Qed.
Lemma lem5352562 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352563 : term322 = term267.
Proof. exact (MK_COMB (@lem5352562) (@lem5352561)). Qed.
Lemma lem5352564 : term321 = term267.
Proof. exact (TRANS (@lem5352559) (@lem5352563)). Qed.
Lemma lem5352566 (x : nat) : (term325 x) = term254.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5352567 : term316 = term254.
Proof. exact (@lem5352566 term146). Qed.
Lemma lem5352568 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5352569 : term326 = term327.
Proof. exact (MK_COMB (@lem5352568) (@lem5352567)). Qed.
Lemma lem5352570 : term318 = term309.
Proof. exact (MK_COMB (@lem5352569) (@lem5352564)). Qed.
Lemma lem5352571 : term317 = term309.
Proof. exact (TRANS (@lem5352556) (@lem5352570)). Qed.
Lemma lem5352572 : term316 = term309.
Proof. exact (TRANS (@lem5352555) (@lem5352571)). Qed.
Lemma lem5352574 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5352575 : term309 = term254.
Proof. exact (@lem5352574 term254). Qed.
Lemma lem5352576 : term316 = term254.
Proof. exact (TRANS (@lem5352572) (@lem5352575)). Qed.
Lemma lem5352577 (_69725 : int) : (term268 _69725) = (term268 _69725).
Proof. exact (eq_refl (term268 _69725)). Qed.
Lemma lem5352578 (_69725 : int) : (term307 _69725) = (term329 _69725).
Proof. exact (MK_COMB (@lem5352577 _69725) (@lem5352576)). Qed.
Lemma lem5352579 (_69725 : int) : (term329 _69725) = (real_of_int _69725).
Proof. exact (@lem1982723 (real_of_int _69725)). Qed.
Lemma lem5352580 (_69725 : int) : (term307 _69725) = (real_of_int _69725).
Proof. exact (TRANS (@lem5352578 _69725) (@lem5352579 _69725)). Qed.
Lemma lem5352582 (_69725 : int) : (term306 _69725) = (real_of_int _69725).
Proof. exact (TRANS (@lem5352546 _69725) (@lem5352580 _69725)). Qed.
Lemma lem5352583 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5352584 (_69725 : int) : (term330 _69725) = (term331 _69725).
Proof. exact (MK_COMB (@lem5352583) (@lem5352582 _69725)). Qed.
Lemma lem5352585 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5352586 (_69725 : int) : (term305 _69725) = (term332 _69725).
Proof. exact (MK_COMB (@lem5352584 _69725) (@lem5352585)). Qed.
Lemma lem5352587 (_69725 : int) : (term257 _69725) = (term332 _69725).
Proof. exact (TRANS (@lem5352540 _69725) (@lem5352586 _69725)). Qed.
Lemma lem5352588 (_69726 : int) : (term257 _69726) = (term305 _69726).
Proof. exact (@lem1988287 (real_of_int _69726) term254). Qed.
Lemma lem5352594 (_69726 : int) : (term306 _69726) = (term307 _69726).
Proof. exact (@lem1982792 (real_of_int _69726) term254). Qed.
Lemma lem5352596 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5352597 : term254 = term309.
Proof. exact (@lem5352596 (NUMERAL 0)). Qed.
Lemma lem5352599 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5352600 : term312 = term313.
Proof. exact (@lem5352599 term146). Qed.
Lemma lem5352601 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5352602 : term314 = term315.
Proof. exact (MK_COMB (@lem5352601) (@lem5352600)). Qed.
Lemma lem5352603 : term316 = term317.
Proof. exact (MK_COMB (@lem5352602) (@lem5352597)). Qed.
Lemma lem5352604 : term317 = term318.
Proof. exact (@lem1981613 term312 term254 term267 term267). Qed.
Lemma lem5352606 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5352607 : term321 = term322.
Proof. exact (@lem5352606 term146 term146). Qed.
Lemma lem5352608 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352609 : term324 = term146.
Proof. exact (EQ_MP (@lem5352608) (@lem940073)). Qed.
Lemma lem5352610 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352611 : term322 = term267.
Proof. exact (MK_COMB (@lem5352610) (@lem5352609)). Qed.
Lemma lem5352612 : term321 = term267.
Proof. exact (TRANS (@lem5352607) (@lem5352611)). Qed.
Lemma lem5352614 (x : nat) : (term325 x) = term254.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5352615 : term316 = term254.
Proof. exact (@lem5352614 term146). Qed.
Lemma lem5352616 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5352617 : term326 = term327.
Proof. exact (MK_COMB (@lem5352616) (@lem5352615)). Qed.
Lemma lem5352618 : term318 = term309.
Proof. exact (MK_COMB (@lem5352617) (@lem5352612)). Qed.
Lemma lem5352619 : term317 = term309.
Proof. exact (TRANS (@lem5352604) (@lem5352618)). Qed.
Lemma lem5352620 : term316 = term309.
Proof. exact (TRANS (@lem5352603) (@lem5352619)). Qed.
Lemma lem5352622 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5352623 : term309 = term254.
Proof. exact (@lem5352622 term254). Qed.
Lemma lem5352624 : term316 = term254.
Proof. exact (TRANS (@lem5352620) (@lem5352623)). Qed.
Lemma lem5352625 (_69726 : int) : (term268 _69726) = (term268 _69726).
Proof. exact (eq_refl (term268 _69726)). Qed.
Lemma lem5352626 (_69726 : int) : (term307 _69726) = (term329 _69726).
Proof. exact (MK_COMB (@lem5352625 _69726) (@lem5352624)). Qed.
Lemma lem5352627 (_69726 : int) : (term329 _69726) = (real_of_int _69726).
Proof. exact (@lem1982723 (real_of_int _69726)). Qed.
Lemma lem5352628 (_69726 : int) : (term307 _69726) = (real_of_int _69726).
Proof. exact (TRANS (@lem5352626 _69726) (@lem5352627 _69726)). Qed.
Lemma lem5352630 (_69726 : int) : (term306 _69726) = (real_of_int _69726).
Proof. exact (TRANS (@lem5352594 _69726) (@lem5352628 _69726)). Qed.
Lemma lem5352631 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5352632 (_69726 : int) : (term330 _69726) = (term331 _69726).
Proof. exact (MK_COMB (@lem5352631) (@lem5352630 _69726)). Qed.
Lemma lem5352633 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5352634 (_69726 : int) : (term305 _69726) = (term332 _69726).
Proof. exact (MK_COMB (@lem5352632 _69726) (@lem5352633)). Qed.
Lemma lem5352635 (_69726 : int) : (term257 _69726) = (term332 _69726).
Proof. exact (TRANS (@lem5352588 _69726) (@lem5352634 _69726)). Qed.
Lemma lem5352636 (_69725 : int) (_69724 : int) : (term249 _69724 _69725) = (term333 _69725 _69724).
Proof. exact (@lem1988287 (real_of_int _69725) (real_of_int _69724)). Qed.
Lemma lem5352642 (_69725 : int) (_69724 : int) : (term334 _69725 _69724) = (term335 _69725 _69724).
Proof. exact (@lem1982792 (real_of_int _69725) (real_of_int _69724)). Qed.
Lemma lem5352647 (_69724 : int) (_69725 : int) : (term335 _69725 _69724) = (term336 _69724 _69725).
Proof. exact (@lem1982761 (term337 _69724) (real_of_int _69725)). Qed.
Lemma lem5352649 (_69724 : int) (_69725 : int) : (term334 _69725 _69724) = (term336 _69724 _69725).
Proof. exact (TRANS (@lem5352642 _69725 _69724) (@lem5352647 _69724 _69725)). Qed.
Lemma lem5352650 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5352651 (_69724 : int) (_69725 : int) : (term338 _69725 _69724) = (term339 _69724 _69725).
Proof. exact (MK_COMB (@lem5352650) (@lem5352649 _69724 _69725)). Qed.
Lemma lem5352652 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5352653 (_69724 : int) (_69725 : int) : (term333 _69725 _69724) = (term340 _69724 _69725).
Proof. exact (MK_COMB (@lem5352651 _69724 _69725) (@lem5352652)). Qed.
Lemma lem5352654 (_69724 : int) (_69725 : int) : (term249 _69724 _69725) = (term340 _69724 _69725).
Proof. exact (TRANS (@lem5352636 _69725 _69724) (@lem5352653 _69724 _69725)). Qed.
Lemma lem5352655 (_69724 : int) (_69726 : int) : (term272 _69726 _69724) = (term341 _69724 _69726).
Proof. exact (@lem1988287 (real_of_int _69724) (term269 _69726)). Qed.
Lemma lem5352667 (_69724 : int) (_69726 : int) : (term342 _69724 _69726) = (term343 _69724 _69726).
Proof. exact (@lem1982792 (real_of_int _69724) (term269 _69726)). Qed.
Lemma lem5352668 (_69726 : int) : (term344 _69726) = (term345 _69726).
Proof. exact (@lem1982781 (real_of_int _69726) term312 term267). Qed.
Lemma lem5352670 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5352671 : term267 = term346.
Proof. exact (@lem5352670 term146). Qed.
Lemma lem5352673 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5352674 : term312 = term313.
Proof. exact (@lem5352673 term146). Qed.
Lemma lem5352675 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5352676 : term314 = term315.
Proof. exact (MK_COMB (@lem5352675) (@lem5352674)). Qed.
Lemma lem5352677 : term347 = term348.
Proof. exact (MK_COMB (@lem5352676) (@lem5352671)). Qed.
Lemma lem5352678 : term348 = term349.
Proof. exact (@lem1981613 term312 term267 term267 term267). Qed.
Lemma lem5352680 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5352681 : term321 = term322.
Proof. exact (@lem5352680 term146 term146). Qed.
Lemma lem5352682 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352683 : term324 = term146.
Proof. exact (EQ_MP (@lem5352682) (@lem940073)). Qed.
Lemma lem5352684 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352685 : term322 = term267.
Proof. exact (MK_COMB (@lem5352684) (@lem5352683)). Qed.
Lemma lem5352686 : term321 = term267.
Proof. exact (TRANS (@lem5352681) (@lem5352685)). Qed.
Lemma lem5352688 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5352689 : term347 = term352.
Proof. exact (@lem5352688 term146 term146). Qed.
Lemma lem5352690 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352691 : term324 = term146.
Proof. exact (EQ_MP (@lem5352690) (@lem940073)). Qed.
Lemma lem5352692 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352693 : term322 = term267.
Proof. exact (MK_COMB (@lem5352692) (@lem5352691)). Qed.
Lemma lem5352694 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5352695 : term352 = term312.
Proof. exact (MK_COMB (@lem5352694) (@lem5352693)). Qed.
Lemma lem5352696 : term347 = term312.
Proof. exact (TRANS (@lem5352689) (@lem5352695)). Qed.
Lemma lem5352697 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5352698 : term353 = term354.
Proof. exact (MK_COMB (@lem5352697) (@lem5352696)). Qed.
Lemma lem5352699 : term349 = term313.
Proof. exact (MK_COMB (@lem5352698) (@lem5352686)). Qed.
Lemma lem5352700 : term348 = term313.
Proof. exact (TRANS (@lem5352678) (@lem5352699)). Qed.
Lemma lem5352701 : term347 = term313.
Proof. exact (TRANS (@lem5352677) (@lem5352700)). Qed.
Lemma lem5352703 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5352704 : term313 = term312.
Proof. exact (@lem5352703 term312). Qed.
Lemma lem5352705 : term347 = term312.
Proof. exact (TRANS (@lem5352701) (@lem5352704)). Qed.
Lemma lem5352708 (_69726 : int) : (term355 _69726) = (term355 _69726).
Proof. exact (eq_refl (term355 _69726)). Qed.
Lemma lem5352709 (_69726 : int) : (term345 _69726) = (term356 _69726).
Proof. exact (MK_COMB (@lem5352708 _69726) (@lem5352705)). Qed.
Lemma lem5352710 (_69726 : int) : (term344 _69726) = (term356 _69726).
Proof. exact (TRANS (@lem5352668 _69726) (@lem5352709 _69726)). Qed.
Lemma lem5352711 (_69724 : int) : (term268 _69724) = (term268 _69724).
Proof. exact (eq_refl (term268 _69724)). Qed.
Lemma lem5352714 (_69724 : int) (_69726 : int) : (term343 _69724 _69726) = (term357 _69724 _69726).
Proof. exact (MK_COMB (@lem5352711 _69724) (@lem5352710 _69726)). Qed.
Lemma lem5352716 (_69724 : int) (_69726 : int) : (term342 _69724 _69726) = (term357 _69724 _69726).
Proof. exact (TRANS (@lem5352667 _69724 _69726) (@lem5352714 _69724 _69726)). Qed.
Lemma lem5352717 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5352718 (_69724 : int) (_69726 : int) : (term358 _69724 _69726) = (term359 _69724 _69726).
Proof. exact (MK_COMB (@lem5352717) (@lem5352716 _69724 _69726)). Qed.
Lemma lem5352719 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5352720 (_69724 : int) (_69726 : int) : (term341 _69724 _69726) = (term360 _69724 _69726).
Proof. exact (MK_COMB (@lem5352718 _69724 _69726) (@lem5352719)). Qed.
Lemma lem5352721 (_69724 : int) (_69726 : int) : (term272 _69726 _69724) = (term360 _69724 _69726).
Proof. exact (TRANS (@lem5352655 _69724 _69726) (@lem5352720 _69724 _69726)). Qed.
Lemma lem5352722 (_69726 : int) (_69724 : int) : (term272 _69724 _69726) = (term341 _69726 _69724).
Proof. exact (@lem1988287 (real_of_int _69726) (term269 _69724)). Qed.
Lemma lem5352734 (_69726 : int) (_69724 : int) : (term342 _69726 _69724) = (term343 _69726 _69724).
Proof. exact (@lem1982792 (real_of_int _69726) (term269 _69724)). Qed.
Lemma lem5352735 (_69724 : int) : (term344 _69724) = (term345 _69724).
Proof. exact (@lem1982781 (real_of_int _69724) term312 term267). Qed.
Lemma lem5352737 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5352738 : term267 = term346.
Proof. exact (@lem5352737 term146). Qed.
Lemma lem5352740 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5352741 : term312 = term313.
Proof. exact (@lem5352740 term146). Qed.
Lemma lem5352742 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5352743 : term314 = term315.
Proof. exact (MK_COMB (@lem5352742) (@lem5352741)). Qed.
Lemma lem5352744 : term347 = term348.
Proof. exact (MK_COMB (@lem5352743) (@lem5352738)). Qed.
Lemma lem5352745 : term348 = term349.
Proof. exact (@lem1981613 term312 term267 term267 term267). Qed.
Lemma lem5352747 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5352748 : term321 = term322.
Proof. exact (@lem5352747 term146 term146). Qed.
Lemma lem5352749 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352750 : term324 = term146.
Proof. exact (EQ_MP (@lem5352749) (@lem940073)). Qed.
Lemma lem5352751 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352752 : term322 = term267.
Proof. exact (MK_COMB (@lem5352751) (@lem5352750)). Qed.
Lemma lem5352753 : term321 = term267.
Proof. exact (TRANS (@lem5352748) (@lem5352752)). Qed.
Lemma lem5352755 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5352756 : term347 = term352.
Proof. exact (@lem5352755 term146 term146). Qed.
Lemma lem5352757 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352758 : term324 = term146.
Proof. exact (EQ_MP (@lem5352757) (@lem940073)). Qed.
Lemma lem5352759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352760 : term322 = term267.
Proof. exact (MK_COMB (@lem5352759) (@lem5352758)). Qed.
Lemma lem5352761 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5352762 : term352 = term312.
Proof. exact (MK_COMB (@lem5352761) (@lem5352760)). Qed.
Lemma lem5352763 : term347 = term312.
Proof. exact (TRANS (@lem5352756) (@lem5352762)). Qed.
Lemma lem5352764 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5352765 : term353 = term354.
Proof. exact (MK_COMB (@lem5352764) (@lem5352763)). Qed.
Lemma lem5352766 : term349 = term313.
Proof. exact (MK_COMB (@lem5352765) (@lem5352753)). Qed.
Lemma lem5352767 : term348 = term313.
Proof. exact (TRANS (@lem5352745) (@lem5352766)). Qed.
Lemma lem5352768 : term347 = term313.
Proof. exact (TRANS (@lem5352744) (@lem5352767)). Qed.
Lemma lem5352770 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5352771 : term313 = term312.
Proof. exact (@lem5352770 term312). Qed.
Lemma lem5352772 : term347 = term312.
Proof. exact (TRANS (@lem5352768) (@lem5352771)). Qed.
Lemma lem5352775 (_69724 : int) : (term355 _69724) = (term355 _69724).
Proof. exact (eq_refl (term355 _69724)). Qed.
Lemma lem5352776 (_69724 : int) : (term345 _69724) = (term356 _69724).
Proof. exact (MK_COMB (@lem5352775 _69724) (@lem5352772)). Qed.
Lemma lem5352777 (_69724 : int) : (term344 _69724) = (term356 _69724).
Proof. exact (TRANS (@lem5352735 _69724) (@lem5352776 _69724)). Qed.
Lemma lem5352778 (_69726 : int) : (term268 _69726) = (term268 _69726).
Proof. exact (eq_refl (term268 _69726)). Qed.
Lemma lem5352779 (_69726 : int) (_69724 : int) : (term343 _69726 _69724) = (term357 _69726 _69724).
Proof. exact (MK_COMB (@lem5352778 _69726) (@lem5352777 _69724)). Qed.
Lemma lem5352784 (_69724 : int) (_69726 : int) : (term357 _69726 _69724) = (term361 _69724 _69726).
Proof. exact (@lem1982757 (term337 _69724) (real_of_int _69726) term312). Qed.
Lemma lem5352785 (_69724 : int) (_69726 : int) : (term343 _69726 _69724) = (term361 _69724 _69726).
Proof. exact (TRANS (@lem5352779 _69726 _69724) (@lem5352784 _69724 _69726)). Qed.
Lemma lem5352787 (_69724 : int) (_69726 : int) : (term342 _69726 _69724) = (term361 _69724 _69726).
Proof. exact (TRANS (@lem5352734 _69726 _69724) (@lem5352785 _69724 _69726)). Qed.
Lemma lem5352788 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5352789 (_69724 : int) (_69726 : int) : (term358 _69726 _69724) = (term362 _69724 _69726).
Proof. exact (MK_COMB (@lem5352788) (@lem5352787 _69724 _69726)). Qed.
Lemma lem5352790 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5352791 (_69724 : int) (_69726 : int) : (term341 _69726 _69724) = (term363 _69724 _69726).
Proof. exact (MK_COMB (@lem5352789 _69724 _69726) (@lem5352790)). Qed.
Lemma lem5352792 (_69724 : int) (_69726 : int) : (term272 _69724 _69726) = (term363 _69724 _69726).
Proof. exact (TRANS (@lem5352722 _69726 _69724) (@lem5352791 _69724 _69726)). Qed.
Lemma lem5352793 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5352794 (_69724 : int) (_69726 : int) : (term274 _69726 _69724) = (term364 _69724 _69726).
Proof. exact (MK_COMB (@lem5352793) (@lem5352721 _69724 _69726)). Qed.
Lemma lem5352795 (_69724 : int) (_69726 : int) : (term275 _69724 _69726) = (term365 _69724 _69726).
Proof. exact (MK_COMB (@lem5352794 _69724 _69726) (@lem5352792 _69724 _69726)). Qed.
Lemma lem5352796 (_69724 : int) (_69726 : int) : (term278 _69726 _69724) = (term366 _69724 _69726).
Proof. exact (@lem1988287 (term269 _69724) (term269 _69726)). Qed.
Lemma lem5352814 (_69724 : int) (_69726 : int) : (term367 _69724 _69726) = (term368 _69724 _69726).
Proof. exact (@lem1982792 (term269 _69724) (term269 _69726)). Qed.
Lemma lem5352815 (_69726 : int) : (term344 _69726) = (term345 _69726).
Proof. exact (@lem1982781 (real_of_int _69726) term312 term267). Qed.
Lemma lem5352817 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5352818 : term267 = term346.
Proof. exact (@lem5352817 term146). Qed.
Lemma lem5352820 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5352821 : term312 = term313.
Proof. exact (@lem5352820 term146). Qed.
Lemma lem5352822 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5352823 : term314 = term315.
Proof. exact (MK_COMB (@lem5352822) (@lem5352821)). Qed.
Lemma lem5352824 : term347 = term348.
Proof. exact (MK_COMB (@lem5352823) (@lem5352818)). Qed.
Lemma lem5352825 : term348 = term349.
Proof. exact (@lem1981613 term312 term267 term267 term267). Qed.
Lemma lem5352827 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5352828 : term321 = term322.
Proof. exact (@lem5352827 term146 term146). Qed.
Lemma lem5352829 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352830 : term324 = term146.
Proof. exact (EQ_MP (@lem5352829) (@lem940073)). Qed.
Lemma lem5352831 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352832 : term322 = term267.
Proof. exact (MK_COMB (@lem5352831) (@lem5352830)). Qed.
Lemma lem5352833 : term321 = term267.
Proof. exact (TRANS (@lem5352828) (@lem5352832)). Qed.
Lemma lem5352835 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5352836 : term347 = term352.
Proof. exact (@lem5352835 term146 term146). Qed.
Lemma lem5352837 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352838 : term324 = term146.
Proof. exact (EQ_MP (@lem5352837) (@lem940073)). Qed.
Lemma lem5352839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352840 : term322 = term267.
Proof. exact (MK_COMB (@lem5352839) (@lem5352838)). Qed.
Lemma lem5352841 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5352842 : term352 = term312.
Proof. exact (MK_COMB (@lem5352841) (@lem5352840)). Qed.
Lemma lem5352843 : term347 = term312.
Proof. exact (TRANS (@lem5352836) (@lem5352842)). Qed.
Lemma lem5352844 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5352845 : term353 = term354.
Proof. exact (MK_COMB (@lem5352844) (@lem5352843)). Qed.
Lemma lem5352846 : term349 = term313.
Proof. exact (MK_COMB (@lem5352845) (@lem5352833)). Qed.
Lemma lem5352847 : term348 = term313.
Proof. exact (TRANS (@lem5352825) (@lem5352846)). Qed.
Lemma lem5352848 : term347 = term313.
Proof. exact (TRANS (@lem5352824) (@lem5352847)). Qed.
Lemma lem5352850 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5352851 : term313 = term312.
Proof. exact (@lem5352850 term312). Qed.
Lemma lem5352852 : term347 = term312.
Proof. exact (TRANS (@lem5352848) (@lem5352851)). Qed.
Lemma lem5352855 (_69726 : int) : (term355 _69726) = (term355 _69726).
Proof. exact (eq_refl (term355 _69726)). Qed.
Lemma lem5352856 (_69726 : int) : (term345 _69726) = (term356 _69726).
Proof. exact (MK_COMB (@lem5352855 _69726) (@lem5352852)). Qed.
Lemma lem5352857 (_69726 : int) : (term344 _69726) = (term356 _69726).
Proof. exact (TRANS (@lem5352815 _69726) (@lem5352856 _69726)). Qed.
Lemma lem5352858 (_69724 : int) : (term369 _69724) = (term369 _69724).
Proof. exact (eq_refl (term369 _69724)). Qed.
Lemma lem5352859 (_69724 : int) (_69726 : int) : (term368 _69724 _69726) = (term370 _69724 _69726).
Proof. exact (MK_COMB (@lem5352858 _69724) (@lem5352857 _69726)). Qed.
Lemma lem5352860 (_69724 : int) (_69726 : int) : (term370 _69724 _69726) = (term371 _69724 _69726).
Proof. exact (@lem1982755 (real_of_int _69724) term267 (term356 _69726)). Qed.
Lemma lem5352861 (_69726 : int) : (term372 _69726) = (term373 _69726).
Proof. exact (@lem1982757 (term337 _69726) term267 term312). Qed.
Lemma lem5352863 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5352864 : term312 = term313.
Proof. exact (@lem5352863 term146). Qed.
Lemma lem5352866 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5352867 : term267 = term346.
Proof. exact (@lem5352866 term146). Qed.
Lemma lem5352868 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5352869 : term374 = term375.
Proof. exact (MK_COMB (@lem5352868) (@lem5352867)). Qed.
Lemma lem5352870 : term376 = term377.
Proof. exact (MK_COMB (@lem5352869) (@lem5352864)). Qed.
Lemma lem5352871 : term378.
Proof. exact (@lem1981473 term267 term267 term312 term267 term254 term267). Qed.
Lemma lem5352873 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5352874 : term380 = term381.
Proof. exact (@lem5352873 (NUMERAL 0) term146). Qed.
Lemma lem5352875 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5352876 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5352877 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5352876 h1) (fun h1 : term381 = True => @lem5352875)). Qed.
Lemma lem5352878 : term381 = True.
Proof. exact (EQ_MP (@lem5352877) (@lem5352875)). Qed.
Lemma lem5352879 : term380 = True.
Proof. exact (TRANS (@lem5352874) (@lem5352878)). Qed.
Lemma lem5352880 : True = term380.
Proof. exact (SYM (@lem5352879)). Qed.
Lemma lem5352881 : term380.
Proof. exact (EQ_MP (@lem5352880) (@lem0)). Qed.
Lemma lem5352882 : term383.
Proof. exact (@lem5352871 (@lem5352881)). Qed.
Lemma lem5352884 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5352885 : term380 = term381.
Proof. exact (@lem5352884 (NUMERAL 0) term146). Qed.
Lemma lem5352886 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5352887 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5352888 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5352887 h1) (fun h1 : term381 = True => @lem5352886)). Qed.
Lemma lem5352889 : term381 = True.
Proof. exact (EQ_MP (@lem5352888) (@lem5352886)). Qed.
Lemma lem5352890 : term380 = True.
Proof. exact (TRANS (@lem5352885) (@lem5352889)). Qed.
Lemma lem5352891 : True = term380.
Proof. exact (SYM (@lem5352890)). Qed.
Lemma lem5352892 : term380.
Proof. exact (EQ_MP (@lem5352891) (@lem0)). Qed.
Lemma lem5352893 : term384.
Proof. exact (@lem5352882 (@lem5352892)). Qed.
Lemma lem5352895 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5352896 : term380 = term381.
Proof. exact (@lem5352895 (NUMERAL 0) term146). Qed.
Lemma lem5352897 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5352898 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5352899 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5352898 h1) (fun h1 : term381 = True => @lem5352897)). Qed.
Lemma lem5352900 : term381 = True.
Proof. exact (EQ_MP (@lem5352899) (@lem5352897)). Qed.
Lemma lem5352901 : term380 = True.
Proof. exact (TRANS (@lem5352896) (@lem5352900)). Qed.
Lemma lem5352902 : True = term380.
Proof. exact (SYM (@lem5352901)). Qed.
Lemma lem5352903 : term380.
Proof. exact (EQ_MP (@lem5352902) (@lem0)). Qed.
Lemma lem5352904 : term385.
Proof. exact (@lem5352893 (@lem5352903)). Qed.
Lemma lem5352906 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5352907 : term347 = term352.
Proof. exact (@lem5352906 term146 term146). Qed.
Lemma lem5352908 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352909 : term324 = term146.
Proof. exact (EQ_MP (@lem5352908) (@lem940073)). Qed.
Lemma lem5352910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352911 : term322 = term267.
Proof. exact (MK_COMB (@lem5352910) (@lem5352909)). Qed.
Lemma lem5352912 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5352913 : term352 = term312.
Proof. exact (MK_COMB (@lem5352912) (@lem5352911)). Qed.
Lemma lem5352914 : term347 = term312.
Proof. exact (TRANS (@lem5352907) (@lem5352913)). Qed.
Lemma lem5352916 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5352917 : term321 = term322.
Proof. exact (@lem5352916 term146 term146). Qed.
Lemma lem5352918 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352919 : term324 = term146.
Proof. exact (EQ_MP (@lem5352918) (@lem940073)). Qed.
Lemma lem5352920 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352921 : term322 = term267.
Proof. exact (MK_COMB (@lem5352920) (@lem5352919)). Qed.
Lemma lem5352922 : term321 = term267.
Proof. exact (TRANS (@lem5352917) (@lem5352921)). Qed.
Lemma lem5352923 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5352924 : term386 = term374.
Proof. exact (MK_COMB (@lem5352923) (@lem5352922)). Qed.
Lemma lem5352925 : term387 = term376.
Proof. exact (MK_COMB (@lem5352924) (@lem5352914)). Qed.
Lemma lem5352927 (m : nat) : (term388 m) = term254.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5352928 : term376 = term254.
Proof. exact (@lem5352927 term146). Qed.
Lemma lem5352929 : term387 = term254.
Proof. exact (TRANS (@lem5352925) (@lem5352928)). Qed.
Lemma lem5352930 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5352931 : term389 = term390.
Proof. exact (MK_COMB (@lem5352930) (@lem5352929)). Qed.
Lemma lem5352932 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5352933 : term391 = term392.
Proof. exact (MK_COMB (@lem5352931) (@lem5352932)). Qed.
Lemma lem5352935 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5352936 : term392 = term254.
Proof. exact (@lem5352935 term146). Qed.
Lemma lem5352937 : term391 = term254.
Proof. exact (TRANS (@lem5352933) (@lem5352936)). Qed.
Lemma lem5352939 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5352940 : term321 = term322.
Proof. exact (@lem5352939 term146 term146). Qed.
Lemma lem5352941 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5352942 : term324 = term146.
Proof. exact (EQ_MP (@lem5352941) (@lem940073)). Qed.
Lemma lem5352943 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5352944 : term322 = term267.
Proof. exact (MK_COMB (@lem5352943) (@lem5352942)). Qed.
Lemma lem5352945 : term321 = term267.
Proof. exact (TRANS (@lem5352940) (@lem5352944)). Qed.
Lemma lem5352946 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5352947 : term394 = term392.
Proof. exact (MK_COMB (@lem5352946) (@lem5352945)). Qed.
Lemma lem5352949 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5352950 : term392 = term254.
Proof. exact (@lem5352949 term146). Qed.
Lemma lem5352951 : term394 = term254.
Proof. exact (TRANS (@lem5352947) (@lem5352950)). Qed.
Lemma lem5352952 : term254 = term394.
Proof. exact (SYM (@lem5352951)). Qed.
Lemma lem5352953 : term391 = term394.
Proof. exact (TRANS (@lem5352937) (@lem5352952)). Qed.
Lemma lem5352954 : term377 = term309.
Proof. exact (@lem5352904 (@lem5352953)). Qed.
Lemma lem5352955 : term376 = term309.
Proof. exact (TRANS (@lem5352870) (@lem5352954)). Qed.
Lemma lem5352957 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5352958 : term309 = term254.
Proof. exact (@lem5352957 term254). Qed.
Lemma lem5352959 : term376 = term254.
Proof. exact (TRANS (@lem5352955) (@lem5352958)). Qed.
Lemma lem5352960 (_69726 : int) : (term355 _69726) = (term355 _69726).
Proof. exact (eq_refl (term355 _69726)). Qed.
Lemma lem5352961 (_69726 : int) : (term373 _69726) = (term395 _69726).
Proof. exact (MK_COMB (@lem5352960 _69726) (@lem5352959)). Qed.
Lemma lem5352962 (_69726 : int) : (term372 _69726) = (term395 _69726).
Proof. exact (TRANS (@lem5352861 _69726) (@lem5352961 _69726)). Qed.
Lemma lem5352963 (_69726 : int) : (term395 _69726) = (term337 _69726).
Proof. exact (@lem1982723 (term337 _69726)). Qed.
Lemma lem5352964 (_69726 : int) : (term372 _69726) = (term337 _69726).
Proof. exact (TRANS (@lem5352962 _69726) (@lem5352963 _69726)). Qed.
Lemma lem5352965 (_69724 : int) : (term268 _69724) = (term268 _69724).
Proof. exact (eq_refl (term268 _69724)). Qed.
Lemma lem5352966 (_69724 : int) (_69726 : int) : (term371 _69724 _69726) = (term335 _69724 _69726).
Proof. exact (MK_COMB (@lem5352965 _69724) (@lem5352964 _69726)). Qed.
Lemma lem5352967 (_69724 : int) (_69726 : int) : (term370 _69724 _69726) = (term335 _69724 _69726).
Proof. exact (TRANS (@lem5352860 _69724 _69726) (@lem5352966 _69724 _69726)). Qed.
Lemma lem5352968 (_69724 : int) (_69726 : int) : (term368 _69724 _69726) = (term335 _69724 _69726).
Proof. exact (TRANS (@lem5352859 _69724 _69726) (@lem5352967 _69724 _69726)). Qed.
Lemma lem5352970 (_69724 : int) (_69726 : int) : (term367 _69724 _69726) = (term335 _69724 _69726).
Proof. exact (TRANS (@lem5352814 _69724 _69726) (@lem5352968 _69724 _69726)). Qed.
Lemma lem5352971 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5352972 (_69724 : int) (_69726 : int) : (term396 _69724 _69726) = (term397 _69724 _69726).
Proof. exact (MK_COMB (@lem5352971) (@lem5352970 _69724 _69726)). Qed.
Lemma lem5352973 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5352974 (_69724 : int) (_69726 : int) : (term366 _69724 _69726) = (term398 _69724 _69726).
Proof. exact (MK_COMB (@lem5352972 _69724 _69726) (@lem5352973)). Qed.
Lemma lem5352975 (_69724 : int) (_69726 : int) : (term278 _69726 _69724) = (term398 _69724 _69726).
Proof. exact (TRANS (@lem5352796 _69724 _69726) (@lem5352974 _69724 _69726)). Qed.
Lemma lem5352976 (_69726 : int) (_69725 : int) : (term272 _69725 _69726) = (term341 _69726 _69725).
Proof. exact (@lem1988287 (real_of_int _69726) (term269 _69725)). Qed.
Lemma lem5352988 (_69726 : int) (_69725 : int) : (term342 _69726 _69725) = (term343 _69726 _69725).
Proof. exact (@lem1982792 (real_of_int _69726) (term269 _69725)). Qed.
Lemma lem5352989 (_69725 : int) : (term344 _69725) = (term345 _69725).
Proof. exact (@lem1982781 (real_of_int _69725) term312 term267). Qed.
Lemma lem5352991 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5352992 : term267 = term346.
Proof. exact (@lem5352991 term146). Qed.
Lemma lem5352994 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5352995 : term312 = term313.
Proof. exact (@lem5352994 term146). Qed.
Lemma lem5352996 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5352997 : term314 = term315.
Proof. exact (MK_COMB (@lem5352996) (@lem5352995)). Qed.
Lemma lem5352998 : term347 = term348.
Proof. exact (MK_COMB (@lem5352997) (@lem5352992)). Qed.
Lemma lem5352999 : term348 = term349.
Proof. exact (@lem1981613 term312 term267 term267 term267). Qed.
Lemma lem5353001 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5353002 : term321 = term322.
Proof. exact (@lem5353001 term146 term146). Qed.
Lemma lem5353003 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353004 : term324 = term146.
Proof. exact (EQ_MP (@lem5353003) (@lem940073)). Qed.
Lemma lem5353005 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353006 : term322 = term267.
Proof. exact (MK_COMB (@lem5353005) (@lem5353004)). Qed.
Lemma lem5353007 : term321 = term267.
Proof. exact (TRANS (@lem5353002) (@lem5353006)). Qed.
Lemma lem5353009 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5353010 : term347 = term352.
Proof. exact (@lem5353009 term146 term146). Qed.
Lemma lem5353011 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353012 : term324 = term146.
Proof. exact (EQ_MP (@lem5353011) (@lem940073)). Qed.
Lemma lem5353013 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353014 : term322 = term267.
Proof. exact (MK_COMB (@lem5353013) (@lem5353012)). Qed.
Lemma lem5353015 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5353016 : term352 = term312.
Proof. exact (MK_COMB (@lem5353015) (@lem5353014)). Qed.
Lemma lem5353017 : term347 = term312.
Proof. exact (TRANS (@lem5353010) (@lem5353016)). Qed.
Lemma lem5353018 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5353019 : term353 = term354.
Proof. exact (MK_COMB (@lem5353018) (@lem5353017)). Qed.
Lemma lem5353020 : term349 = term313.
Proof. exact (MK_COMB (@lem5353019) (@lem5353007)). Qed.
Lemma lem5353021 : term348 = term313.
Proof. exact (TRANS (@lem5352999) (@lem5353020)). Qed.
Lemma lem5353022 : term347 = term313.
Proof. exact (TRANS (@lem5352998) (@lem5353021)). Qed.
Lemma lem5353024 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5353025 : term313 = term312.
Proof. exact (@lem5353024 term312). Qed.
Lemma lem5353026 : term347 = term312.
Proof. exact (TRANS (@lem5353022) (@lem5353025)). Qed.
Lemma lem5353029 (_69725 : int) : (term355 _69725) = (term355 _69725).
Proof. exact (eq_refl (term355 _69725)). Qed.
Lemma lem5353030 (_69725 : int) : (term345 _69725) = (term356 _69725).
Proof. exact (MK_COMB (@lem5353029 _69725) (@lem5353026)). Qed.
Lemma lem5353031 (_69725 : int) : (term344 _69725) = (term356 _69725).
Proof. exact (TRANS (@lem5352989 _69725) (@lem5353030 _69725)). Qed.
Lemma lem5353032 (_69726 : int) : (term268 _69726) = (term268 _69726).
Proof. exact (eq_refl (term268 _69726)). Qed.
Lemma lem5353033 (_69726 : int) (_69725 : int) : (term343 _69726 _69725) = (term357 _69726 _69725).
Proof. exact (MK_COMB (@lem5353032 _69726) (@lem5353031 _69725)). Qed.
Lemma lem5353038 (_69725 : int) (_69726 : int) : (term357 _69726 _69725) = (term361 _69725 _69726).
Proof. exact (@lem1982757 (term337 _69725) (real_of_int _69726) term312). Qed.
Lemma lem5353039 (_69725 : int) (_69726 : int) : (term343 _69726 _69725) = (term361 _69725 _69726).
Proof. exact (TRANS (@lem5353033 _69726 _69725) (@lem5353038 _69725 _69726)). Qed.
Lemma lem5353041 (_69725 : int) (_69726 : int) : (term342 _69726 _69725) = (term361 _69725 _69726).
Proof. exact (TRANS (@lem5352988 _69726 _69725) (@lem5353039 _69725 _69726)). Qed.
Lemma lem5353042 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5353043 (_69725 : int) (_69726 : int) : (term358 _69726 _69725) = (term362 _69725 _69726).
Proof. exact (MK_COMB (@lem5353042) (@lem5353041 _69725 _69726)). Qed.
Lemma lem5353044 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5353045 (_69725 : int) (_69726 : int) : (term341 _69726 _69725) = (term363 _69725 _69726).
Proof. exact (MK_COMB (@lem5353043 _69725 _69726) (@lem5353044)). Qed.
Lemma lem5353046 (_69725 : int) (_69726 : int) : (term272 _69725 _69726) = (term363 _69725 _69726).
Proof. exact (TRANS (@lem5352976 _69726 _69725) (@lem5353045 _69725 _69726)). Qed.
Lemma lem5353047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353048 (_69724 : int) (_69726 : int) : (term280 _69726 _69724) = (term399 _69724 _69726).
Proof. exact (MK_COMB (@lem5353047) (@lem5352975 _69724 _69726)). Qed.
Lemma lem5353049 (_69724 : int) (_69725 : int) (_69726 : int) : (term281 _69724 _69725 _69726) = (term400 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353048 _69724 _69726) (@lem5353046 _69725 _69726)). Qed.
Lemma lem5353050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5353051 (_69724 : int) (_69726 : int) : (term282 _69724 _69726) = (term401 _69724 _69726).
Proof. exact (MK_COMB (@lem5353050) (@lem5352795 _69724 _69726)). Qed.
Lemma lem5353052 (_69724 : int) (_69725 : int) (_69726 : int) : (term283 _69724 _69725 _69726) = (term402 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353051 _69724 _69726) (@lem5353049 _69724 _69725 _69726)). Qed.
Lemma lem5353053 (_69726 : int) (_69724 : int) : (term249 _69724 _69726) = (term333 _69726 _69724).
Proof. exact (@lem1988287 (real_of_int _69726) (real_of_int _69724)). Qed.
Lemma lem5353059 (_69726 : int) (_69724 : int) : (term334 _69726 _69724) = (term335 _69726 _69724).
Proof. exact (@lem1982792 (real_of_int _69726) (real_of_int _69724)). Qed.
Lemma lem5353064 (_69724 : int) (_69726 : int) : (term335 _69726 _69724) = (term336 _69724 _69726).
Proof. exact (@lem1982761 (term337 _69724) (real_of_int _69726)). Qed.
Lemma lem5353066 (_69724 : int) (_69726 : int) : (term334 _69726 _69724) = (term336 _69724 _69726).
Proof. exact (TRANS (@lem5353059 _69726 _69724) (@lem5353064 _69724 _69726)). Qed.
Lemma lem5353067 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5353068 (_69724 : int) (_69726 : int) : (term338 _69726 _69724) = (term339 _69724 _69726).
Proof. exact (MK_COMB (@lem5353067) (@lem5353066 _69724 _69726)). Qed.
Lemma lem5353069 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5353070 (_69724 : int) (_69726 : int) : (term333 _69726 _69724) = (term340 _69724 _69726).
Proof. exact (MK_COMB (@lem5353068 _69724 _69726) (@lem5353069)). Qed.
Lemma lem5353071 (_69724 : int) (_69726 : int) : (term249 _69724 _69726) = (term340 _69724 _69726).
Proof. exact (TRANS (@lem5353053 _69726 _69724) (@lem5353070 _69724 _69726)). Qed.
Lemma lem5353072 (_69725 : int) (_69726 : int) : (term249 _69726 _69725) = (term333 _69725 _69726).
Proof. exact (@lem1988287 (real_of_int _69725) (real_of_int _69726)). Qed.
Lemma lem5353085 (_69725 : int) (_69726 : int) : (term334 _69725 _69726) = (term335 _69725 _69726).
Proof. exact (@lem1982792 (real_of_int _69725) (real_of_int _69726)). Qed.
Lemma lem5353086 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5353087 (_69725 : int) (_69726 : int) : (term338 _69725 _69726) = (term397 _69725 _69726).
Proof. exact (MK_COMB (@lem5353086) (@lem5353085 _69725 _69726)). Qed.
Lemma lem5353088 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5353089 (_69725 : int) (_69726 : int) : (term333 _69725 _69726) = (term398 _69725 _69726).
Proof. exact (MK_COMB (@lem5353087 _69725 _69726) (@lem5353088)). Qed.
Lemma lem5353090 (_69725 : int) (_69726 : int) : (term249 _69726 _69725) = (term398 _69725 _69726).
Proof. exact (TRANS (@lem5353072 _69725 _69726) (@lem5353089 _69725 _69726)). Qed.
Lemma lem5353091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5353092 (_69724 : int) (_69726 : int) : (term284 _69724 _69726) = (term403 _69724 _69726).
Proof. exact (MK_COMB (@lem5353091) (@lem5353071 _69724 _69726)). Qed.
Lemma lem5353093 (_69724 : int) (_69725 : int) (_69726 : int) : (term285 _69724 _69726 _69725) = (term404 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353092 _69724 _69726) (@lem5353090 _69725 _69726)). Qed.
Lemma lem5353094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5353095 (_69724 : int) (_69725 : int) (_69726 : int) : (term286 _69724 _69725 _69726) = (term405 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353094) (@lem5353052 _69724 _69725 _69726)). Qed.
Lemma lem5353096 (_69724 : int) (_69725 : int) (_69726 : int) : (term287 _69724 _69726 _69725) = (term406 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353095 _69724 _69725 _69726) (@lem5353093 _69724 _69725 _69726)). Qed.
Lemma lem5353097 (_69726 : int) (_69724 : int) : ((real_of_int _69726) = (real_of_int _69724)) = ((term334 _69726 _69724) = term254).
Proof. exact (@lem1988293 (real_of_int _69726) (real_of_int _69724)). Qed.
Lemma lem5353103 (_69726 : int) (_69724 : int) : (term334 _69726 _69724) = (term335 _69726 _69724).
Proof. exact (@lem1982792 (real_of_int _69726) (real_of_int _69724)). Qed.
Lemma lem5353108 (_69724 : int) (_69726 : int) : (term335 _69726 _69724) = (term336 _69724 _69726).
Proof. exact (@lem1982761 (term337 _69724) (real_of_int _69726)). Qed.
Lemma lem5353110 (_69724 : int) (_69726 : int) : (term334 _69726 _69724) = (term336 _69724 _69726).
Proof. exact (TRANS (@lem5353103 _69726 _69724) (@lem5353108 _69724 _69726)). Qed.
Lemma lem5353111 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5353112 (_69724 : int) (_69726 : int) : (term407 _69726 _69724) = (term408 _69724 _69726).
Proof. exact (MK_COMB (@lem5353111) (@lem5353110 _69724 _69726)). Qed.
Lemma lem5353113 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5353114 (_69724 : int) (_69726 : int) : ((term334 _69726 _69724) = term254) = ((term336 _69724 _69726) = term254).
Proof. exact (MK_COMB (@lem5353112 _69724 _69726) (@lem5353113)). Qed.
Lemma lem5353115 (_69724 : int) (_69726 : int) : ((real_of_int _69726) = (real_of_int _69724)) = ((term336 _69724 _69726) = term254).
Proof. exact (TRANS (@lem5353097 _69726 _69724) (@lem5353114 _69724 _69726)). Qed.
Lemma lem5353116 (_69726 : int) (_69724 : int) : (term272 _69724 _69726) = (term341 _69726 _69724).
Proof. exact (@lem1988287 (real_of_int _69726) (term269 _69724)). Qed.
Lemma lem5353128 (_69726 : int) (_69724 : int) : (term342 _69726 _69724) = (term343 _69726 _69724).
Proof. exact (@lem1982792 (real_of_int _69726) (term269 _69724)). Qed.
Lemma lem5353129 (_69724 : int) : (term344 _69724) = (term345 _69724).
Proof. exact (@lem1982781 (real_of_int _69724) term312 term267). Qed.
Lemma lem5353131 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5353132 : term267 = term346.
Proof. exact (@lem5353131 term146). Qed.
Lemma lem5353134 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5353135 : term312 = term313.
Proof. exact (@lem5353134 term146). Qed.
Lemma lem5353136 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5353137 : term314 = term315.
Proof. exact (MK_COMB (@lem5353136) (@lem5353135)). Qed.
Lemma lem5353138 : term347 = term348.
Proof. exact (MK_COMB (@lem5353137) (@lem5353132)). Qed.
Lemma lem5353139 : term348 = term349.
Proof. exact (@lem1981613 term312 term267 term267 term267). Qed.
Lemma lem5353141 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5353142 : term321 = term322.
Proof. exact (@lem5353141 term146 term146). Qed.
Lemma lem5353143 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353144 : term324 = term146.
Proof. exact (EQ_MP (@lem5353143) (@lem940073)). Qed.
Lemma lem5353145 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353146 : term322 = term267.
Proof. exact (MK_COMB (@lem5353145) (@lem5353144)). Qed.
Lemma lem5353147 : term321 = term267.
Proof. exact (TRANS (@lem5353142) (@lem5353146)). Qed.
Lemma lem5353149 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5353150 : term347 = term352.
Proof. exact (@lem5353149 term146 term146). Qed.
Lemma lem5353151 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353152 : term324 = term146.
Proof. exact (EQ_MP (@lem5353151) (@lem940073)). Qed.
Lemma lem5353153 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353154 : term322 = term267.
Proof. exact (MK_COMB (@lem5353153) (@lem5353152)). Qed.
Lemma lem5353155 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5353156 : term352 = term312.
Proof. exact (MK_COMB (@lem5353155) (@lem5353154)). Qed.
Lemma lem5353157 : term347 = term312.
Proof. exact (TRANS (@lem5353150) (@lem5353156)). Qed.
Lemma lem5353158 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5353159 : term353 = term354.
Proof. exact (MK_COMB (@lem5353158) (@lem5353157)). Qed.
Lemma lem5353160 : term349 = term313.
Proof. exact (MK_COMB (@lem5353159) (@lem5353147)). Qed.
Lemma lem5353161 : term348 = term313.
Proof. exact (TRANS (@lem5353139) (@lem5353160)). Qed.
Lemma lem5353162 : term347 = term313.
Proof. exact (TRANS (@lem5353138) (@lem5353161)). Qed.
Lemma lem5353164 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5353165 : term313 = term312.
Proof. exact (@lem5353164 term312). Qed.
Lemma lem5353166 : term347 = term312.
Proof. exact (TRANS (@lem5353162) (@lem5353165)). Qed.
Lemma lem5353169 (_69724 : int) : (term355 _69724) = (term355 _69724).
Proof. exact (eq_refl (term355 _69724)). Qed.
Lemma lem5353170 (_69724 : int) : (term345 _69724) = (term356 _69724).
Proof. exact (MK_COMB (@lem5353169 _69724) (@lem5353166)). Qed.
Lemma lem5353171 (_69724 : int) : (term344 _69724) = (term356 _69724).
Proof. exact (TRANS (@lem5353129 _69724) (@lem5353170 _69724)). Qed.
Lemma lem5353172 (_69726 : int) : (term268 _69726) = (term268 _69726).
Proof. exact (eq_refl (term268 _69726)). Qed.
Lemma lem5353173 (_69726 : int) (_69724 : int) : (term343 _69726 _69724) = (term357 _69726 _69724).
Proof. exact (MK_COMB (@lem5353172 _69726) (@lem5353171 _69724)). Qed.
Lemma lem5353178 (_69724 : int) (_69726 : int) : (term357 _69726 _69724) = (term361 _69724 _69726).
Proof. exact (@lem1982757 (term337 _69724) (real_of_int _69726) term312). Qed.
Lemma lem5353179 (_69724 : int) (_69726 : int) : (term343 _69726 _69724) = (term361 _69724 _69726).
Proof. exact (TRANS (@lem5353173 _69726 _69724) (@lem5353178 _69724 _69726)). Qed.
Lemma lem5353181 (_69724 : int) (_69726 : int) : (term342 _69726 _69724) = (term361 _69724 _69726).
Proof. exact (TRANS (@lem5353128 _69726 _69724) (@lem5353179 _69724 _69726)). Qed.
Lemma lem5353182 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5353183 (_69724 : int) (_69726 : int) : (term358 _69726 _69724) = (term362 _69724 _69726).
Proof. exact (MK_COMB (@lem5353182) (@lem5353181 _69724 _69726)). Qed.
Lemma lem5353184 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5353185 (_69724 : int) (_69726 : int) : (term341 _69726 _69724) = (term363 _69724 _69726).
Proof. exact (MK_COMB (@lem5353183 _69724 _69726) (@lem5353184)). Qed.
Lemma lem5353186 (_69724 : int) (_69726 : int) : (term272 _69724 _69726) = (term363 _69724 _69726).
Proof. exact (TRANS (@lem5353116 _69726 _69724) (@lem5353185 _69724 _69726)). Qed.
Lemma lem5353187 (_69725 : int) (_69726 : int) : (term249 _69726 _69725) = (term333 _69725 _69726).
Proof. exact (@lem1988287 (real_of_int _69725) (real_of_int _69726)). Qed.
Lemma lem5353200 (_69725 : int) (_69726 : int) : (term334 _69725 _69726) = (term335 _69725 _69726).
Proof. exact (@lem1982792 (real_of_int _69725) (real_of_int _69726)). Qed.
Lemma lem5353201 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5353202 (_69725 : int) (_69726 : int) : (term338 _69725 _69726) = (term397 _69725 _69726).
Proof. exact (MK_COMB (@lem5353201) (@lem5353200 _69725 _69726)). Qed.
Lemma lem5353203 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5353204 (_69725 : int) (_69726 : int) : (term333 _69725 _69726) = (term398 _69725 _69726).
Proof. exact (MK_COMB (@lem5353202 _69725 _69726) (@lem5353203)). Qed.
Lemma lem5353205 (_69725 : int) (_69726 : int) : (term249 _69726 _69725) = (term398 _69725 _69726).
Proof. exact (TRANS (@lem5353187 _69725 _69726) (@lem5353204 _69725 _69726)). Qed.
Lemma lem5353206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5353207 (_69724 : int) (_69726 : int) : (term288 _69724 _69726) = (term409 _69724 _69726).
Proof. exact (MK_COMB (@lem5353206) (@lem5353186 _69724 _69726)). Qed.
Lemma lem5353208 (_69724 : int) (_69725 : int) (_69726 : int) : (term289 _69724 _69726 _69725) = (term410 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353207 _69724 _69726) (@lem5353205 _69725 _69726)). Qed.
Lemma lem5353209 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353210 (_69724 : int) (_69726 : int) : (term290 _69726 _69724) = (term411 _69724 _69726).
Proof. exact (MK_COMB (@lem5353209) (@lem5353115 _69724 _69726)). Qed.
Lemma lem5353211 (_69724 : int) (_69725 : int) (_69726 : int) : (term291 _69724 _69726 _69725) = (term412 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353210 _69724 _69726) (@lem5353208 _69724 _69725 _69726)). Qed.
Lemma lem5353212 (_69724 : int) (_69726 : int) : (term272 _69726 _69724) = (term341 _69724 _69726).
Proof. exact (@lem1988287 (real_of_int _69724) (term269 _69726)). Qed.
Lemma lem5353224 (_69724 : int) (_69726 : int) : (term342 _69724 _69726) = (term343 _69724 _69726).
Proof. exact (@lem1982792 (real_of_int _69724) (term269 _69726)). Qed.
Lemma lem5353225 (_69726 : int) : (term344 _69726) = (term345 _69726).
Proof. exact (@lem1982781 (real_of_int _69726) term312 term267). Qed.
Lemma lem5353227 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5353228 : term267 = term346.
Proof. exact (@lem5353227 term146). Qed.
Lemma lem5353230 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5353231 : term312 = term313.
Proof. exact (@lem5353230 term146). Qed.
Lemma lem5353232 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5353233 : term314 = term315.
Proof. exact (MK_COMB (@lem5353232) (@lem5353231)). Qed.
Lemma lem5353234 : term347 = term348.
Proof. exact (MK_COMB (@lem5353233) (@lem5353228)). Qed.
Lemma lem5353235 : term348 = term349.
Proof. exact (@lem1981613 term312 term267 term267 term267). Qed.
Lemma lem5353237 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5353238 : term321 = term322.
Proof. exact (@lem5353237 term146 term146). Qed.
Lemma lem5353239 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353240 : term324 = term146.
Proof. exact (EQ_MP (@lem5353239) (@lem940073)). Qed.
Lemma lem5353241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353242 : term322 = term267.
Proof. exact (MK_COMB (@lem5353241) (@lem5353240)). Qed.
Lemma lem5353243 : term321 = term267.
Proof. exact (TRANS (@lem5353238) (@lem5353242)). Qed.
Lemma lem5353245 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5353246 : term347 = term352.
Proof. exact (@lem5353245 term146 term146). Qed.
Lemma lem5353247 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353248 : term324 = term146.
Proof. exact (EQ_MP (@lem5353247) (@lem940073)). Qed.
Lemma lem5353249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353250 : term322 = term267.
Proof. exact (MK_COMB (@lem5353249) (@lem5353248)). Qed.
Lemma lem5353251 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5353252 : term352 = term312.
Proof. exact (MK_COMB (@lem5353251) (@lem5353250)). Qed.
Lemma lem5353253 : term347 = term312.
Proof. exact (TRANS (@lem5353246) (@lem5353252)). Qed.
Lemma lem5353254 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5353255 : term353 = term354.
Proof. exact (MK_COMB (@lem5353254) (@lem5353253)). Qed.
Lemma lem5353256 : term349 = term313.
Proof. exact (MK_COMB (@lem5353255) (@lem5353243)). Qed.
Lemma lem5353257 : term348 = term313.
Proof. exact (TRANS (@lem5353235) (@lem5353256)). Qed.
Lemma lem5353258 : term347 = term313.
Proof. exact (TRANS (@lem5353234) (@lem5353257)). Qed.
Lemma lem5353260 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5353261 : term313 = term312.
Proof. exact (@lem5353260 term312). Qed.
Lemma lem5353262 : term347 = term312.
Proof. exact (TRANS (@lem5353258) (@lem5353261)). Qed.
Lemma lem5353265 (_69726 : int) : (term355 _69726) = (term355 _69726).
Proof. exact (eq_refl (term355 _69726)). Qed.
Lemma lem5353266 (_69726 : int) : (term345 _69726) = (term356 _69726).
Proof. exact (MK_COMB (@lem5353265 _69726) (@lem5353262)). Qed.
Lemma lem5353267 (_69726 : int) : (term344 _69726) = (term356 _69726).
Proof. exact (TRANS (@lem5353225 _69726) (@lem5353266 _69726)). Qed.
Lemma lem5353268 (_69724 : int) : (term268 _69724) = (term268 _69724).
Proof. exact (eq_refl (term268 _69724)). Qed.
Lemma lem5353271 (_69724 : int) (_69726 : int) : (term343 _69724 _69726) = (term357 _69724 _69726).
Proof. exact (MK_COMB (@lem5353268 _69724) (@lem5353267 _69726)). Qed.
Lemma lem5353273 (_69724 : int) (_69726 : int) : (term342 _69724 _69726) = (term357 _69724 _69726).
Proof. exact (TRANS (@lem5353224 _69724 _69726) (@lem5353271 _69724 _69726)). Qed.
Lemma lem5353274 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5353275 (_69724 : int) (_69726 : int) : (term358 _69724 _69726) = (term359 _69724 _69726).
Proof. exact (MK_COMB (@lem5353274) (@lem5353273 _69724 _69726)). Qed.
Lemma lem5353276 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5353277 (_69724 : int) (_69726 : int) : (term341 _69724 _69726) = (term360 _69724 _69726).
Proof. exact (MK_COMB (@lem5353275 _69724 _69726) (@lem5353276)). Qed.
Lemma lem5353278 (_69724 : int) (_69726 : int) : (term272 _69726 _69724) = (term360 _69724 _69726).
Proof. exact (TRANS (@lem5353212 _69724 _69726) (@lem5353277 _69724 _69726)). Qed.
Lemma lem5353279 (_69726 : int) (_69725 : int) : (term272 _69725 _69726) = (term341 _69726 _69725).
Proof. exact (@lem1988287 (real_of_int _69726) (term269 _69725)). Qed.
Lemma lem5353291 (_69726 : int) (_69725 : int) : (term342 _69726 _69725) = (term343 _69726 _69725).
Proof. exact (@lem1982792 (real_of_int _69726) (term269 _69725)). Qed.
Lemma lem5353292 (_69725 : int) : (term344 _69725) = (term345 _69725).
Proof. exact (@lem1982781 (real_of_int _69725) term312 term267). Qed.
Lemma lem5353294 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5353295 : term267 = term346.
Proof. exact (@lem5353294 term146). Qed.
Lemma lem5353297 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5353298 : term312 = term313.
Proof. exact (@lem5353297 term146). Qed.
Lemma lem5353299 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5353300 : term314 = term315.
Proof. exact (MK_COMB (@lem5353299) (@lem5353298)). Qed.
Lemma lem5353301 : term347 = term348.
Proof. exact (MK_COMB (@lem5353300) (@lem5353295)). Qed.
Lemma lem5353302 : term348 = term349.
Proof. exact (@lem1981613 term312 term267 term267 term267). Qed.
Lemma lem5353304 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5353305 : term321 = term322.
Proof. exact (@lem5353304 term146 term146). Qed.
Lemma lem5353306 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353307 : term324 = term146.
Proof. exact (EQ_MP (@lem5353306) (@lem940073)). Qed.
Lemma lem5353308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353309 : term322 = term267.
Proof. exact (MK_COMB (@lem5353308) (@lem5353307)). Qed.
Lemma lem5353310 : term321 = term267.
Proof. exact (TRANS (@lem5353305) (@lem5353309)). Qed.
Lemma lem5353312 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5353313 : term347 = term352.
Proof. exact (@lem5353312 term146 term146). Qed.
Lemma lem5353314 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353315 : term324 = term146.
Proof. exact (EQ_MP (@lem5353314) (@lem940073)). Qed.
Lemma lem5353316 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353317 : term322 = term267.
Proof. exact (MK_COMB (@lem5353316) (@lem5353315)). Qed.
Lemma lem5353318 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5353319 : term352 = term312.
Proof. exact (MK_COMB (@lem5353318) (@lem5353317)). Qed.
Lemma lem5353320 : term347 = term312.
Proof. exact (TRANS (@lem5353313) (@lem5353319)). Qed.
Lemma lem5353321 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5353322 : term353 = term354.
Proof. exact (MK_COMB (@lem5353321) (@lem5353320)). Qed.
Lemma lem5353323 : term349 = term313.
Proof. exact (MK_COMB (@lem5353322) (@lem5353310)). Qed.
Lemma lem5353324 : term348 = term313.
Proof. exact (TRANS (@lem5353302) (@lem5353323)). Qed.
Lemma lem5353325 : term347 = term313.
Proof. exact (TRANS (@lem5353301) (@lem5353324)). Qed.
Lemma lem5353327 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5353328 : term313 = term312.
Proof. exact (@lem5353327 term312). Qed.
Lemma lem5353329 : term347 = term312.
Proof. exact (TRANS (@lem5353325) (@lem5353328)). Qed.
Lemma lem5353332 (_69725 : int) : (term355 _69725) = (term355 _69725).
Proof. exact (eq_refl (term355 _69725)). Qed.
Lemma lem5353333 (_69725 : int) : (term345 _69725) = (term356 _69725).
Proof. exact (MK_COMB (@lem5353332 _69725) (@lem5353329)). Qed.
Lemma lem5353334 (_69725 : int) : (term344 _69725) = (term356 _69725).
Proof. exact (TRANS (@lem5353292 _69725) (@lem5353333 _69725)). Qed.
Lemma lem5353335 (_69726 : int) : (term268 _69726) = (term268 _69726).
Proof. exact (eq_refl (term268 _69726)). Qed.
Lemma lem5353336 (_69726 : int) (_69725 : int) : (term343 _69726 _69725) = (term357 _69726 _69725).
Proof. exact (MK_COMB (@lem5353335 _69726) (@lem5353334 _69725)). Qed.
Lemma lem5353341 (_69725 : int) (_69726 : int) : (term357 _69726 _69725) = (term361 _69725 _69726).
Proof. exact (@lem1982757 (term337 _69725) (real_of_int _69726) term312). Qed.
Lemma lem5353342 (_69725 : int) (_69726 : int) : (term343 _69726 _69725) = (term361 _69725 _69726).
Proof. exact (TRANS (@lem5353336 _69726 _69725) (@lem5353341 _69725 _69726)). Qed.
Lemma lem5353344 (_69725 : int) (_69726 : int) : (term342 _69726 _69725) = (term361 _69725 _69726).
Proof. exact (TRANS (@lem5353291 _69726 _69725) (@lem5353342 _69725 _69726)). Qed.
Lemma lem5353345 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5353346 (_69725 : int) (_69726 : int) : (term358 _69726 _69725) = (term362 _69725 _69726).
Proof. exact (MK_COMB (@lem5353345) (@lem5353344 _69725 _69726)). Qed.
Lemma lem5353347 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5353348 (_69725 : int) (_69726 : int) : (term341 _69726 _69725) = (term363 _69725 _69726).
Proof. exact (MK_COMB (@lem5353346 _69725 _69726) (@lem5353347)). Qed.
Lemma lem5353349 (_69725 : int) (_69726 : int) : (term272 _69725 _69726) = (term363 _69725 _69726).
Proof. exact (TRANS (@lem5353279 _69726 _69725) (@lem5353348 _69725 _69726)). Qed.
Lemma lem5353350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353351 (_69724 : int) (_69726 : int) : (term274 _69726 _69724) = (term364 _69724 _69726).
Proof. exact (MK_COMB (@lem5353350) (@lem5353278 _69724 _69726)). Qed.
Lemma lem5353352 (_69724 : int) (_69725 : int) (_69726 : int) : (term293 _69724 _69725 _69726) = (term413 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353351 _69724 _69726) (@lem5353349 _69725 _69726)). Qed.
Lemma lem5353353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5353354 (_69724 : int) (_69725 : int) (_69726 : int) : (term294 _69724 _69726 _69725) = (term414 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353353) (@lem5353211 _69724 _69725 _69726)). Qed.
Lemma lem5353355 (_69724 : int) (_69725 : int) (_69726 : int) : (term295 _69724 _69725 _69726) = (term415 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353354 _69724 _69725 _69726) (@lem5353352 _69724 _69725 _69726)). Qed.
Lemma lem5353356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353357 (_69724 : int) (_69725 : int) (_69726 : int) : (term296 _69724 _69726 _69725) = (term416 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353356) (@lem5353096 _69724 _69725 _69726)). Qed.
Lemma lem5353358 (_69724 : int) (_69725 : int) (_69726 : int) : (term297 _69724 _69725 _69726) = (term417 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353357 _69724 _69725 _69726) (@lem5353355 _69724 _69725 _69726)). Qed.
Lemma lem5353359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5353360 (_69724 : int) (_69725 : int) : (term284 _69724 _69725) = (term403 _69724 _69725).
Proof. exact (MK_COMB (@lem5353359) (@lem5352654 _69724 _69725)). Qed.
Lemma lem5353361 (_69724 : int) (_69725 : int) (_69726 : int) : (term298 _69724 _69725 _69726) = (term418 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353360 _69724 _69725) (@lem5353358 _69724 _69725 _69726)). Qed.
Lemma lem5353362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5353363 (_69726 : int) : (term299 _69726) = (term419 _69726).
Proof. exact (MK_COMB (@lem5353362) (@lem5352635 _69726)). Qed.
Lemma lem5353364 (_69724 : int) (_69725 : int) (_69726 : int) : (term300 _69724 _69725 _69726) = (term420 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353363 _69726) (@lem5353361 _69724 _69725 _69726)). Qed.
Lemma lem5353365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5353366 (_69725 : int) : (term299 _69725) = (term419 _69725).
Proof. exact (MK_COMB (@lem5353365) (@lem5352587 _69725)). Qed.
Lemma lem5353367 (_69724 : int) (_69725 : int) (_69726 : int) : (term301 _69724 _69725 _69726) = (term421 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353366 _69725) (@lem5353364 _69724 _69725 _69726)). Qed.
Lemma lem5353368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5353369 (_69724 : int) : (term299 _69724) = (term419 _69724).
Proof. exact (MK_COMB (@lem5353368) (@lem5352539 _69724)). Qed.
Lemma lem5353370 (_69724 : int) (_69725 : int) (_69726 : int) : (term302 _69724 _69725 _69726) = (term422 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353369 _69724) (@lem5353367 _69724 _69725 _69726)). Qed.
Lemma lem5353377 (_69724 : int) (_69725 : int) (_69726 : int) : (term304 _69724 _69725 _69726) = (term422 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5352491 _69724 _69725 _69726) (@lem5353370 _69724 _69725 _69726)). Qed.
Lemma lem5353397 (_69724 : int) (_69725 : int) (_69726 : int) : (term415 _69724 _69725 _69726) = (term423 _69724 _69725 _69726).
Proof. exact (@lem19158 (term360 _69724 _69726) (term412 _69724 _69725 _69726) (term363 _69725 _69726)). Qed.
Lemma lem5353404 (_69724 : int) (_69725 : int) (_69726 : int) : (term424 _69724 _69725 _69726) = (term425 _69724 _69725 _69726).
Proof. exact (@lem19367 ((term336 _69724 _69726) = term254) (term410 _69724 _69725 _69726) (term363 _69725 _69726)). Qed.
Lemma lem5353411 (_69725 : int) (_69724 : int) (_69726 : int) : (term426 _69725 _69724 _69726) = (term427 _69725 _69724 _69726).
Proof. exact (@lem19367 ((term336 _69724 _69726) = term254) (term410 _69724 _69725 _69726) (term360 _69724 _69726)). Qed.
Lemma lem5353412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353413 (_69725 : int) (_69724 : int) (_69726 : int) : (term428 _69725 _69724 _69726) = (term429 _69725 _69724 _69726).
Proof. exact (MK_COMB (@lem5353412) (@lem5353411 _69725 _69724 _69726)). Qed.
Lemma lem5353414 (_69724 : int) (_69725 : int) (_69726 : int) : (term423 _69724 _69725 _69726) = (term430 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353413 _69725 _69724 _69726) (@lem5353404 _69724 _69725 _69726)). Qed.
Lemma lem5353416 (_69724 : int) (_69725 : int) (_69726 : int) : (term415 _69724 _69725 _69726) = (term430 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353397 _69724 _69725 _69726) (@lem5353414 _69724 _69725 _69726)). Qed.
Lemma lem5353423 (_69724 : int) (_69725 : int) (_69726 : int) : (term404 _69724 _69725 _69726) = (term404 _69724 _69725 _69726).
Proof. exact (eq_refl (term404 _69724 _69725 _69726)). Qed.
Lemma lem5353437 (_69724 : int) (_69725 : int) (_69726 : int) : (term402 _69724 _69725 _69726) = (term431 _69724 _69725 _69726).
Proof. exact (@lem19158 (term398 _69724 _69726) (term365 _69724 _69726) (term363 _69725 _69726)). Qed.
Lemma lem5353444 (_69724 : int) (_69725 : int) (_69726 : int) : (term432 _69724 _69725 _69726) = (term433 _69724 _69725 _69726).
Proof. exact (@lem19367 (term360 _69724 _69726) (term363 _69724 _69726) (term363 _69725 _69726)). Qed.
Lemma lem5353451 (_69724 : int) (_69726 : int) : (term434 _69724 _69726) = (term435 _69724 _69726).
Proof. exact (@lem19367 (term360 _69724 _69726) (term363 _69724 _69726) (term398 _69724 _69726)). Qed.
Lemma lem5353452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353453 (_69724 : int) (_69726 : int) : (term436 _69724 _69726) = (term437 _69724 _69726).
Proof. exact (MK_COMB (@lem5353452) (@lem5353451 _69724 _69726)). Qed.
Lemma lem5353454 (_69724 : int) (_69725 : int) (_69726 : int) : (term431 _69724 _69725 _69726) = (term438 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353453 _69724 _69726) (@lem5353444 _69724 _69725 _69726)). Qed.
Lemma lem5353456 (_69724 : int) (_69725 : int) (_69726 : int) : (term402 _69724 _69725 _69726) = (term438 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353437 _69724 _69725 _69726) (@lem5353454 _69724 _69725 _69726)). Qed.
Lemma lem5353457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5353458 (_69724 : int) (_69725 : int) (_69726 : int) : (term405 _69724 _69725 _69726) = (term439 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353457) (@lem5353456 _69724 _69725 _69726)). Qed.
Lemma lem5353459 (_69724 : int) (_69725 : int) (_69726 : int) : (term406 _69724 _69725 _69726) = (term440 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353458 _69724 _69725 _69726) (@lem5353423 _69724 _69725 _69726)). Qed.
Lemma lem5353460 (_69724 : int) (_69725 : int) (_69726 : int) : (term440 _69724 _69725 _69726) = (term441 _69724 _69725 _69726).
Proof. exact (@lem19367 (term435 _69724 _69726) (term433 _69724 _69725 _69726) (term404 _69724 _69725 _69726)). Qed.
Lemma lem5353467 (_69724 : int) (_69725 : int) (_69726 : int) : (term442 _69724 _69725 _69726) = (term443 _69724 _69725 _69726).
Proof. exact (@lem19367 (term444 _69724 _69725 _69726) (term445 _69724 _69725 _69726) (term404 _69724 _69725 _69726)). Qed.
Lemma lem5353474 (_69724 : int) (_69725 : int) (_69726 : int) : (term446 _69724 _69725 _69726) = (term447 _69724 _69725 _69726).
Proof. exact (@lem19367 (term448 _69724 _69726) (term449 _69724 _69726) (term404 _69724 _69725 _69726)). Qed.
Lemma lem5353475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353476 (_69724 : int) (_69725 : int) (_69726 : int) : (term450 _69724 _69725 _69726) = (term451 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353475) (@lem5353474 _69724 _69725 _69726)). Qed.
Lemma lem5353477 (_69724 : int) (_69725 : int) (_69726 : int) : (term441 _69724 _69725 _69726) = (term452 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353476 _69724 _69725 _69726) (@lem5353467 _69724 _69725 _69726)). Qed.
Lemma lem5353478 (_69724 : int) (_69725 : int) (_69726 : int) : (term440 _69724 _69725 _69726) = (term452 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353460 _69724 _69725 _69726) (@lem5353477 _69724 _69725 _69726)). Qed.
Lemma lem5353479 (_69724 : int) (_69725 : int) (_69726 : int) : (term406 _69724 _69725 _69726) = (term452 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353459 _69724 _69725 _69726) (@lem5353478 _69724 _69725 _69726)). Qed.
Lemma lem5353480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353481 (_69724 : int) (_69725 : int) (_69726 : int) : (term416 _69724 _69725 _69726) = (term453 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353480) (@lem5353479 _69724 _69725 _69726)). Qed.
Lemma lem5353482 (_69724 : int) (_69725 : int) (_69726 : int) : (term417 _69724 _69725 _69726) = (term454 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353481 _69724 _69725 _69726) (@lem5353416 _69724 _69725 _69726)). Qed.
Lemma lem5353485 (_69724 : int) (_69725 : int) : (term403 _69724 _69725) = (term403 _69724 _69725).
Proof. exact (eq_refl (term403 _69724 _69725)). Qed.
Lemma lem5353486 (_69724 : int) (_69725 : int) (_69726 : int) : (term418 _69724 _69725 _69726) = (term455 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353485 _69724 _69725) (@lem5353482 _69724 _69725 _69726)). Qed.
Lemma lem5353487 (_69724 : int) (_69725 : int) (_69726 : int) : (term455 _69724 _69725 _69726) = (term456 _69724 _69725 _69726).
Proof. exact (@lem19158 (term452 _69724 _69725 _69726) (term340 _69724 _69725) (term430 _69724 _69725 _69726)). Qed.
Lemma lem5353488 (_69724 : int) (_69725 : int) (_69726 : int) : (term457 _69724 _69725 _69726) = (term458 _69724 _69725 _69726).
Proof. exact (@lem19158 (term427 _69725 _69724 _69726) (term340 _69724 _69725) (term425 _69724 _69725 _69726)). Qed.
Lemma lem5353495 (_69724 : int) (_69725 : int) (_69726 : int) : (term459 _69724 _69725 _69726) = (term460 _69724 _69725 _69726).
Proof. exact (@lem19158 (term461 _69724 _69725 _69726) (term340 _69724 _69725) (term462 _69724 _69725 _69726)). Qed.
Lemma lem5353502 (_69725 : int) (_69724 : int) (_69726 : int) : (term463 _69725 _69724 _69726) = (term464 _69725 _69724 _69726).
Proof. exact (@lem19158 (term465 _69724 _69726) (term340 _69724 _69725) (term466 _69725 _69724 _69726)). Qed.
Lemma lem5353503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353504 (_69725 : int) (_69724 : int) (_69726 : int) : (term467 _69725 _69724 _69726) = (term468 _69725 _69724 _69726).
Proof. exact (MK_COMB (@lem5353503) (@lem5353502 _69725 _69724 _69726)). Qed.
Lemma lem5353505 (_69724 : int) (_69725 : int) (_69726 : int) : (term458 _69724 _69725 _69726) = (term469 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353504 _69725 _69724 _69726) (@lem5353495 _69724 _69725 _69726)). Qed.
Lemma lem5353506 (_69724 : int) (_69725 : int) (_69726 : int) : (term457 _69724 _69725 _69726) = (term469 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353488 _69724 _69725 _69726) (@lem5353505 _69724 _69725 _69726)). Qed.
Lemma lem5353507 (_69724 : int) (_69725 : int) (_69726 : int) : (term470 _69724 _69725 _69726) = (term471 _69724 _69725 _69726).
Proof. exact (@lem19158 (term447 _69724 _69725 _69726) (term340 _69724 _69725) (term443 _69724 _69725 _69726)). Qed.
Lemma lem5353514 (_69724 : int) (_69725 : int) (_69726 : int) : (term472 _69724 _69725 _69726) = (term473 _69724 _69725 _69726).
Proof. exact (@lem19158 (term474 _69724 _69725 _69726) (term340 _69724 _69725) (term475 _69724 _69725 _69726)). Qed.
Lemma lem5353521 (_69724 : int) (_69725 : int) (_69726 : int) : (term476 _69724 _69725 _69726) = (term477 _69724 _69725 _69726).
Proof. exact (@lem19158 (term478 _69724 _69725 _69726) (term340 _69724 _69725) (term479 _69724 _69725 _69726)). Qed.
Lemma lem5353522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353523 (_69724 : int) (_69725 : int) (_69726 : int) : (term480 _69724 _69725 _69726) = (term481 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353522) (@lem5353521 _69724 _69725 _69726)). Qed.
Lemma lem5353524 (_69724 : int) (_69725 : int) (_69726 : int) : (term471 _69724 _69725 _69726) = (term482 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353523 _69724 _69725 _69726) (@lem5353514 _69724 _69725 _69726)). Qed.
Lemma lem5353525 (_69724 : int) (_69725 : int) (_69726 : int) : (term470 _69724 _69725 _69726) = (term482 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353507 _69724 _69725 _69726) (@lem5353524 _69724 _69725 _69726)). Qed.
Lemma lem5353526 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353527 (_69724 : int) (_69725 : int) (_69726 : int) : (term483 _69724 _69725 _69726) = (term484 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353526) (@lem5353525 _69724 _69725 _69726)). Qed.
Lemma lem5353528 (_69724 : int) (_69725 : int) (_69726 : int) : (term456 _69724 _69725 _69726) = (term485 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353527 _69724 _69725 _69726) (@lem5353506 _69724 _69725 _69726)). Qed.
Lemma lem5353529 (_69724 : int) (_69725 : int) (_69726 : int) : (term455 _69724 _69725 _69726) = (term485 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353487 _69724 _69725 _69726) (@lem5353528 _69724 _69725 _69726)). Qed.
Lemma lem5353530 (_69724 : int) (_69725 : int) (_69726 : int) : (term418 _69724 _69725 _69726) = (term485 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353486 _69724 _69725 _69726) (@lem5353529 _69724 _69725 _69726)). Qed.
Lemma lem5353533 (_69726 : int) : (term419 _69726) = (term419 _69726).
Proof. exact (eq_refl (term419 _69726)). Qed.
Lemma lem5353534 (_69724 : int) (_69725 : int) (_69726 : int) : (term420 _69724 _69725 _69726) = (term486 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353533 _69726) (@lem5353530 _69724 _69725 _69726)). Qed.
Lemma lem5353535 (_69724 : int) (_69725 : int) (_69726 : int) : (term486 _69724 _69725 _69726) = (term487 _69724 _69725 _69726).
Proof. exact (@lem19158 (term482 _69724 _69725 _69726) (term332 _69726) (term469 _69724 _69725 _69726)). Qed.
Lemma lem5353536 (_69724 : int) (_69725 : int) (_69726 : int) : (term488 _69724 _69725 _69726) = (term489 _69724 _69725 _69726).
Proof. exact (@lem19158 (term464 _69725 _69724 _69726) (term332 _69726) (term460 _69724 _69725 _69726)). Qed.
Lemma lem5353543 (_69724 : int) (_69725 : int) (_69726 : int) : (term490 _69724 _69725 _69726) = (term491 _69724 _69725 _69726).
Proof. exact (@lem19158 (term492 _69724 _69725 _69726) (term332 _69726) (term493 _69724 _69725 _69726)). Qed.
Lemma lem5353550 (_69725 : int) (_69724 : int) (_69726 : int) : (term494 _69725 _69724 _69726) = (term495 _69725 _69724 _69726).
Proof. exact (@lem19158 (term496 _69725 _69724 _69726) (term332 _69726) (term497 _69725 _69724 _69726)). Qed.
Lemma lem5353551 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353552 (_69725 : int) (_69724 : int) (_69726 : int) : (term498 _69725 _69724 _69726) = (term499 _69725 _69724 _69726).
Proof. exact (MK_COMB (@lem5353551) (@lem5353550 _69725 _69724 _69726)). Qed.
Lemma lem5353553 (_69724 : int) (_69725 : int) (_69726 : int) : (term489 _69724 _69725 _69726) = (term500 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353552 _69725 _69724 _69726) (@lem5353543 _69724 _69725 _69726)). Qed.
Lemma lem5353554 (_69724 : int) (_69725 : int) (_69726 : int) : (term488 _69724 _69725 _69726) = (term500 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353536 _69724 _69725 _69726) (@lem5353553 _69724 _69725 _69726)). Qed.
Lemma lem5353555 (_69724 : int) (_69725 : int) (_69726 : int) : (term501 _69724 _69725 _69726) = (term502 _69724 _69725 _69726).
Proof. exact (@lem19158 (term477 _69724 _69725 _69726) (term332 _69726) (term473 _69724 _69725 _69726)). Qed.
Lemma lem5353562 (_69724 : int) (_69725 : int) (_69726 : int) : (term503 _69724 _69725 _69726) = (term504 _69724 _69725 _69726).
Proof. exact (@lem19158 (term505 _69724 _69725 _69726) (term332 _69726) (term506 _69724 _69725 _69726)). Qed.
Lemma lem5353569 (_69724 : int) (_69725 : int) (_69726 : int) : (term507 _69724 _69725 _69726) = (term508 _69724 _69725 _69726).
Proof. exact (@lem19158 (term509 _69724 _69725 _69726) (term332 _69726) (term510 _69724 _69725 _69726)). Qed.
Lemma lem5353570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353571 (_69724 : int) (_69725 : int) (_69726 : int) : (term511 _69724 _69725 _69726) = (term512 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353570) (@lem5353569 _69724 _69725 _69726)). Qed.
Lemma lem5353572 (_69724 : int) (_69725 : int) (_69726 : int) : (term502 _69724 _69725 _69726) = (term513 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353571 _69724 _69725 _69726) (@lem5353562 _69724 _69725 _69726)). Qed.
Lemma lem5353573 (_69724 : int) (_69725 : int) (_69726 : int) : (term501 _69724 _69725 _69726) = (term513 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353555 _69724 _69725 _69726) (@lem5353572 _69724 _69725 _69726)). Qed.
Lemma lem5353574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353575 (_69724 : int) (_69725 : int) (_69726 : int) : (term514 _69724 _69725 _69726) = (term515 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353574) (@lem5353573 _69724 _69725 _69726)). Qed.
Lemma lem5353576 (_69724 : int) (_69725 : int) (_69726 : int) : (term487 _69724 _69725 _69726) = (term516 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353575 _69724 _69725 _69726) (@lem5353554 _69724 _69725 _69726)). Qed.
Lemma lem5353577 (_69724 : int) (_69725 : int) (_69726 : int) : (term486 _69724 _69725 _69726) = (term516 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353535 _69724 _69725 _69726) (@lem5353576 _69724 _69725 _69726)). Qed.
Lemma lem5353578 (_69724 : int) (_69725 : int) (_69726 : int) : (term420 _69724 _69725 _69726) = (term516 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353534 _69724 _69725 _69726) (@lem5353577 _69724 _69725 _69726)). Qed.
Lemma lem5353581 (_69725 : int) : (term419 _69725) = (term419 _69725).
Proof. exact (eq_refl (term419 _69725)). Qed.
Lemma lem5353582 (_69724 : int) (_69725 : int) (_69726 : int) : (term421 _69724 _69725 _69726) = (term517 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353581 _69725) (@lem5353578 _69724 _69725 _69726)). Qed.
Lemma lem5353583 (_69724 : int) (_69725 : int) (_69726 : int) : (term517 _69724 _69725 _69726) = (term518 _69724 _69725 _69726).
Proof. exact (@lem19158 (term513 _69724 _69725 _69726) (term332 _69725) (term500 _69724 _69725 _69726)). Qed.
Lemma lem5353584 (_69724 : int) (_69725 : int) (_69726 : int) : (term519 _69724 _69725 _69726) = (term520 _69724 _69725 _69726).
Proof. exact (@lem19158 (term495 _69725 _69724 _69726) (term332 _69725) (term491 _69724 _69725 _69726)). Qed.
Lemma lem5353591 (_69724 : int) (_69725 : int) (_69726 : int) : (term521 _69724 _69725 _69726) = (term522 _69724 _69725 _69726).
Proof. exact (@lem19158 (term523 _69724 _69725 _69726) (term332 _69725) (term524 _69724 _69725 _69726)). Qed.
Lemma lem5353598 (_69725 : int) (_69724 : int) (_69726 : int) : (term525 _69725 _69724 _69726) = (term526 _69725 _69724 _69726).
Proof. exact (@lem19158 (term527 _69725 _69724 _69726) (term332 _69725) (term528 _69725 _69724 _69726)). Qed.
Lemma lem5353599 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353600 (_69725 : int) (_69724 : int) (_69726 : int) : (term529 _69725 _69724 _69726) = (term530 _69725 _69724 _69726).
Proof. exact (MK_COMB (@lem5353599) (@lem5353598 _69725 _69724 _69726)). Qed.
Lemma lem5353601 (_69724 : int) (_69725 : int) (_69726 : int) : (term520 _69724 _69725 _69726) = (term531 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353600 _69725 _69724 _69726) (@lem5353591 _69724 _69725 _69726)). Qed.
Lemma lem5353602 (_69724 : int) (_69725 : int) (_69726 : int) : (term519 _69724 _69725 _69726) = (term531 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353584 _69724 _69725 _69726) (@lem5353601 _69724 _69725 _69726)). Qed.
Lemma lem5353603 (_69724 : int) (_69725 : int) (_69726 : int) : (term532 _69724 _69725 _69726) = (term533 _69724 _69725 _69726).
Proof. exact (@lem19158 (term508 _69724 _69725 _69726) (term332 _69725) (term504 _69724 _69725 _69726)). Qed.
Lemma lem5353610 (_69724 : int) (_69725 : int) (_69726 : int) : (term534 _69724 _69725 _69726) = (term535 _69724 _69725 _69726).
Proof. exact (@lem19158 (term536 _69724 _69725 _69726) (term332 _69725) (term537 _69724 _69725 _69726)). Qed.
Lemma lem5353617 (_69724 : int) (_69725 : int) (_69726 : int) : (term538 _69724 _69725 _69726) = (term539 _69724 _69725 _69726).
Proof. exact (@lem19158 (term540 _69724 _69725 _69726) (term332 _69725) (term541 _69724 _69725 _69726)). Qed.
Lemma lem5353618 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353619 (_69724 : int) (_69725 : int) (_69726 : int) : (term542 _69724 _69725 _69726) = (term543 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353618) (@lem5353617 _69724 _69725 _69726)). Qed.
Lemma lem5353620 (_69724 : int) (_69725 : int) (_69726 : int) : (term533 _69724 _69725 _69726) = (term544 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353619 _69724 _69725 _69726) (@lem5353610 _69724 _69725 _69726)). Qed.
Lemma lem5353621 (_69724 : int) (_69725 : int) (_69726 : int) : (term532 _69724 _69725 _69726) = (term544 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353603 _69724 _69725 _69726) (@lem5353620 _69724 _69725 _69726)). Qed.
Lemma lem5353622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353623 (_69724 : int) (_69725 : int) (_69726 : int) : (term545 _69724 _69725 _69726) = (term546 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353622) (@lem5353621 _69724 _69725 _69726)). Qed.
Lemma lem5353624 (_69724 : int) (_69725 : int) (_69726 : int) : (term518 _69724 _69725 _69726) = (term547 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353623 _69724 _69725 _69726) (@lem5353602 _69724 _69725 _69726)). Qed.
Lemma lem5353625 (_69724 : int) (_69725 : int) (_69726 : int) : (term517 _69724 _69725 _69726) = (term547 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353583 _69724 _69725 _69726) (@lem5353624 _69724 _69725 _69726)). Qed.
Lemma lem5353626 (_69724 : int) (_69725 : int) (_69726 : int) : (term421 _69724 _69725 _69726) = (term547 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353582 _69724 _69725 _69726) (@lem5353625 _69724 _69725 _69726)). Qed.
Lemma lem5353629 (_69724 : int) : (term419 _69724) = (term419 _69724).
Proof. exact (eq_refl (term419 _69724)). Qed.
Lemma lem5353630 (_69724 : int) (_69725 : int) (_69726 : int) : (term422 _69724 _69725 _69726) = (term548 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353629 _69724) (@lem5353626 _69724 _69725 _69726)). Qed.
Lemma lem5353631 (_69724 : int) (_69725 : int) (_69726 : int) : (term548 _69724 _69725 _69726) = (term549 _69724 _69725 _69726).
Proof. exact (@lem19158 (term544 _69724 _69725 _69726) (term332 _69724) (term531 _69724 _69725 _69726)). Qed.
Lemma lem5353632 (_69724 : int) (_69725 : int) (_69726 : int) : (term550 _69724 _69725 _69726) = (term551 _69724 _69725 _69726).
Proof. exact (@lem19158 (term526 _69725 _69724 _69726) (term332 _69724) (term522 _69724 _69725 _69726)). Qed.
Lemma lem5353639 (_69724 : int) (_69725 : int) (_69726 : int) : (term552 _69724 _69725 _69726) = (term553 _69724 _69725 _69726).
Proof. exact (@lem19158 (term554 _69724 _69725 _69726) (term332 _69724) (term555 _69724 _69725 _69726)). Qed.
Lemma lem5353646 (_69725 : int) (_69724 : int) (_69726 : int) : (term556 _69725 _69724 _69726) = (term557 _69725 _69724 _69726).
Proof. exact (@lem19158 (term558 _69725 _69724 _69726) (term332 _69724) (term559 _69725 _69724 _69726)). Qed.
Lemma lem5353647 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353648 (_69725 : int) (_69724 : int) (_69726 : int) : (term560 _69725 _69724 _69726) = (term561 _69725 _69724 _69726).
Proof. exact (MK_COMB (@lem5353647) (@lem5353646 _69725 _69724 _69726)). Qed.
Lemma lem5353649 (_69724 : int) (_69725 : int) (_69726 : int) : (term551 _69724 _69725 _69726) = (term562 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353648 _69725 _69724 _69726) (@lem5353639 _69724 _69725 _69726)). Qed.
Lemma lem5353650 (_69724 : int) (_69725 : int) (_69726 : int) : (term550 _69724 _69725 _69726) = (term562 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353632 _69724 _69725 _69726) (@lem5353649 _69724 _69725 _69726)). Qed.
Lemma lem5353651 (_69724 : int) (_69725 : int) (_69726 : int) : (term563 _69724 _69725 _69726) = (term564 _69724 _69725 _69726).
Proof. exact (@lem19158 (term539 _69724 _69725 _69726) (term332 _69724) (term535 _69724 _69725 _69726)). Qed.
Lemma lem5353658 (_69724 : int) (_69725 : int) (_69726 : int) : (term565 _69724 _69725 _69726) = (term566 _69724 _69725 _69726).
Proof. exact (@lem19158 (term567 _69724 _69725 _69726) (term332 _69724) (term568 _69724 _69725 _69726)). Qed.
Lemma lem5353665 (_69724 : int) (_69725 : int) (_69726 : int) : (term569 _69724 _69725 _69726) = (term570 _69724 _69725 _69726).
Proof. exact (@lem19158 (term571 _69724 _69725 _69726) (term332 _69724) (term572 _69724 _69725 _69726)). Qed.
Lemma lem5353666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353667 (_69724 : int) (_69725 : int) (_69726 : int) : (term573 _69724 _69725 _69726) = (term574 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353666) (@lem5353665 _69724 _69725 _69726)). Qed.
Lemma lem5353668 (_69724 : int) (_69725 : int) (_69726 : int) : (term564 _69724 _69725 _69726) = (term575 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353667 _69724 _69725 _69726) (@lem5353658 _69724 _69725 _69726)). Qed.
Lemma lem5353669 (_69724 : int) (_69725 : int) (_69726 : int) : (term563 _69724 _69725 _69726) = (term575 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353651 _69724 _69725 _69726) (@lem5353668 _69724 _69725 _69726)). Qed.
Lemma lem5353670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5353671 (_69724 : int) (_69725 : int) (_69726 : int) : (term576 _69724 _69725 _69726) = (term577 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353670) (@lem5353669 _69724 _69725 _69726)). Qed.
Lemma lem5353672 (_69724 : int) (_69725 : int) (_69726 : int) : (term549 _69724 _69725 _69726) = (term578 _69724 _69725 _69726).
Proof. exact (MK_COMB (@lem5353671 _69724 _69725 _69726) (@lem5353650 _69724 _69725 _69726)). Qed.
Lemma lem5353673 (_69724 : int) (_69725 : int) (_69726 : int) : (term548 _69724 _69725 _69726) = (term578 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353631 _69724 _69725 _69726) (@lem5353672 _69724 _69725 _69726)). Qed.
Lemma lem5353674 (_69724 : int) (_69725 : int) (_69726 : int) : (term422 _69724 _69725 _69726) = (term578 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353630 _69724 _69725 _69726) (@lem5353673 _69724 _69725 _69726)). Qed.
Lemma lem5353675 (_69724 : int) (_69725 : int) (_69726 : int) : (term304 _69724 _69725 _69726) = (term578 _69724 _69725 _69726).
Proof. exact (TRANS (@lem5353377 _69724 _69725 _69726) (@lem5353674 _69724 _69725 _69726)). Qed.
Lemma lem5353721 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term578 _69724 _69725 _69726) : term578 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5353722 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term575 _69724 _69725 _69726) : term575 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5353723 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term570 _69724 _69725 _69726) : term570 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5353724 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term579 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5353725 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term571 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5353724 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353727 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term540 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5353725 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353729 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term509 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5353727 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353731 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term478 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5353729 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353733 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term404 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5353731 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353734 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term448 _69724 _69726.
Proof. exact (proj1 (@lem5353731 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353736 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term360 _69724 _69726.
Proof. exact (proj1 (@lem5353734 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353738 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term340 _69724 _69726.
Proof. exact (proj1 (@lem5353733 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353740 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5353741 : term580 = term380.
Proof. exact (@lem5353740 term254 term267). Qed.
Lemma lem5353743 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5353744 : term267 = term346.
Proof. exact (@lem5353743 term146). Qed.
Lemma lem5353746 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5353747 : term254 = term309.
Proof. exact (@lem5353746 (NUMERAL 0)). Qed.
Lemma lem5353748 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5353749 : term581 = term582.
Proof. exact (MK_COMB (@lem5353748) (@lem5353747)). Qed.
Lemma lem5353750 : term380 = term583.
Proof. exact (MK_COMB (@lem5353749) (@lem5353744)). Qed.
Lemma lem5353751 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5353753 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5353754 : term380 = term381.
Proof. exact (@lem5353753 (NUMERAL 0) term146). Qed.
Lemma lem5353755 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5353756 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5353757 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5353756 h1) (fun h1 : term381 = True => @lem5353755)). Qed.
Lemma lem5353758 : term381 = True.
Proof. exact (EQ_MP (@lem5353757) (@lem5353755)). Qed.
Lemma lem5353759 : term380 = True.
Proof. exact (TRANS (@lem5353754) (@lem5353758)). Qed.
Lemma lem5353760 : True = term380.
Proof. exact (SYM (@lem5353759)). Qed.
Lemma lem5353761 : term380.
Proof. exact (EQ_MP (@lem5353760) (@lem0)). Qed.
Lemma lem5353762 : term585.
Proof. exact (@lem5353751 (@lem5353761)). Qed.
Lemma lem5353764 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5353765 : term380 = term381.
Proof. exact (@lem5353764 (NUMERAL 0) term146). Qed.
Lemma lem5353766 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5353767 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5353768 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5353767 h1) (fun h1 : term381 = True => @lem5353766)). Qed.
Lemma lem5353769 : term381 = True.
Proof. exact (EQ_MP (@lem5353768) (@lem5353766)). Qed.
Lemma lem5353770 : term380 = True.
Proof. exact (TRANS (@lem5353765) (@lem5353769)). Qed.
Lemma lem5353771 : True = term380.
Proof. exact (SYM (@lem5353770)). Qed.
Lemma lem5353772 : term380.
Proof. exact (EQ_MP (@lem5353771) (@lem0)). Qed.
Lemma lem5353773 : term583 = term586.
Proof. exact (@lem5353762 (@lem5353772)). Qed.
Lemma lem5353775 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5353776 : term321 = term322.
Proof. exact (@lem5353775 term146 term146). Qed.
Lemma lem5353777 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353778 : term324 = term146.
Proof. exact (EQ_MP (@lem5353777) (@lem940073)). Qed.
Lemma lem5353779 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353780 : term322 = term267.
Proof. exact (MK_COMB (@lem5353779) (@lem5353778)). Qed.
Lemma lem5353781 : term321 = term267.
Proof. exact (TRANS (@lem5353776) (@lem5353780)). Qed.
Lemma lem5353783 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5353784 : term392 = term254.
Proof. exact (@lem5353783 term146). Qed.
Lemma lem5353785 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5353786 : term587 = term581.
Proof. exact (MK_COMB (@lem5353785) (@lem5353784)). Qed.
Lemma lem5353787 : term586 = term380.
Proof. exact (MK_COMB (@lem5353786) (@lem5353781)). Qed.
Lemma lem5353789 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5353790 : term380 = term381.
Proof. exact (@lem5353789 (NUMERAL 0) term146). Qed.
Lemma lem5353791 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5353792 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5353793 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5353792 h1) (fun h1 : term381 = True => @lem5353791)). Qed.
Lemma lem5353794 : term381 = True.
Proof. exact (EQ_MP (@lem5353793) (@lem5353791)). Qed.
Lemma lem5353795 : term380 = True.
Proof. exact (TRANS (@lem5353790) (@lem5353794)). Qed.
Lemma lem5353796 : term586 = True.
Proof. exact (TRANS (@lem5353787) (@lem5353795)). Qed.
Lemma lem5353797 : term583 = True.
Proof. exact (TRANS (@lem5353773) (@lem5353796)). Qed.
Lemma lem5353798 : term380 = True.
Proof. exact (TRANS (@lem5353750) (@lem5353797)). Qed.
Lemma lem5353799 : term580 = True.
Proof. exact (TRANS (@lem5353741) (@lem5353798)). Qed.
Lemma lem5353800 : True = term580.
Proof. exact (SYM (@lem5353799)). Qed.
Lemma lem5353801 : term580.
Proof. exact (EQ_MP (@lem5353800) (@lem0)). Qed.
Lemma lem5353802 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term588 _69724 _69726.
Proof. exact (conj (@lem5353801) (@lem5353736 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353804 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5353805 (_69724 : int) (_69726 : int) : term590 _69724 _69726.
Proof. exact (@lem5353804 term267 (term357 _69724 _69726)). Qed.
Lemma lem5353806 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term591 _69724 _69726.
Proof. exact (@lem5353805 _69724 _69726 (@lem5353802 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353807 (_69724 : int) (_69726 : int) : (term592 _69724 _69726) = (term357 _69724 _69726).
Proof. exact (@lem1982733 (term357 _69724 _69726)). Qed.
Lemma lem5353808 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5353809 (_69724 : int) (_69726 : int) : (term593 _69724 _69726) = (term359 _69724 _69726).
Proof. exact (MK_COMB (@lem5353808) (@lem5353807 _69724 _69726)). Qed.
Lemma lem5353810 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5353811 (_69724 : int) (_69726 : int) : (term591 _69724 _69726) = (term360 _69724 _69726).
Proof. exact (MK_COMB (@lem5353809 _69724 _69726) (@lem5353810)). Qed.
Lemma lem5353812 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term360 _69724 _69726.
Proof. exact (EQ_MP (@lem5353811 _69724 _69726) (@lem5353806 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353814 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5353815 : term580 = term380.
Proof. exact (@lem5353814 term254 term267). Qed.
Lemma lem5353817 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5353818 : term267 = term346.
Proof. exact (@lem5353817 term146). Qed.
Lemma lem5353820 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5353821 : term254 = term309.
Proof. exact (@lem5353820 (NUMERAL 0)). Qed.
Lemma lem5353822 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5353823 : term581 = term582.
Proof. exact (MK_COMB (@lem5353822) (@lem5353821)). Qed.
Lemma lem5353824 : term380 = term583.
Proof. exact (MK_COMB (@lem5353823) (@lem5353818)). Qed.
Lemma lem5353825 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5353827 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5353828 : term380 = term381.
Proof. exact (@lem5353827 (NUMERAL 0) term146). Qed.
Lemma lem5353829 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5353830 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5353831 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5353830 h1) (fun h1 : term381 = True => @lem5353829)). Qed.
Lemma lem5353832 : term381 = True.
Proof. exact (EQ_MP (@lem5353831) (@lem5353829)). Qed.
Lemma lem5353833 : term380 = True.
Proof. exact (TRANS (@lem5353828) (@lem5353832)). Qed.
Lemma lem5353834 : True = term380.
Proof. exact (SYM (@lem5353833)). Qed.
Lemma lem5353835 : term380.
Proof. exact (EQ_MP (@lem5353834) (@lem0)). Qed.
Lemma lem5353836 : term585.
Proof. exact (@lem5353825 (@lem5353835)). Qed.
Lemma lem5353838 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5353839 : term380 = term381.
Proof. exact (@lem5353838 (NUMERAL 0) term146). Qed.
Lemma lem5353840 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5353841 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5353842 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5353841 h1) (fun h1 : term381 = True => @lem5353840)). Qed.
Lemma lem5353843 : term381 = True.
Proof. exact (EQ_MP (@lem5353842) (@lem5353840)). Qed.
Lemma lem5353844 : term380 = True.
Proof. exact (TRANS (@lem5353839) (@lem5353843)). Qed.
Lemma lem5353845 : True = term380.
Proof. exact (SYM (@lem5353844)). Qed.
Lemma lem5353846 : term380.
Proof. exact (EQ_MP (@lem5353845) (@lem0)). Qed.
Lemma lem5353847 : term583 = term586.
Proof. exact (@lem5353836 (@lem5353846)). Qed.
Lemma lem5353849 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5353850 : term321 = term322.
Proof. exact (@lem5353849 term146 term146). Qed.
Lemma lem5353851 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353852 : term324 = term146.
Proof. exact (EQ_MP (@lem5353851) (@lem940073)). Qed.
Lemma lem5353853 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353854 : term322 = term267.
Proof. exact (MK_COMB (@lem5353853) (@lem5353852)). Qed.
Lemma lem5353855 : term321 = term267.
Proof. exact (TRANS (@lem5353850) (@lem5353854)). Qed.
Lemma lem5353857 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5353858 : term392 = term254.
Proof. exact (@lem5353857 term146). Qed.
Lemma lem5353859 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5353860 : term587 = term581.
Proof. exact (MK_COMB (@lem5353859) (@lem5353858)). Qed.
Lemma lem5353861 : term586 = term380.
Proof. exact (MK_COMB (@lem5353860) (@lem5353855)). Qed.
Lemma lem5353863 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5353864 : term380 = term381.
Proof. exact (@lem5353863 (NUMERAL 0) term146). Qed.
Lemma lem5353865 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5353866 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5353867 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5353866 h1) (fun h1 : term381 = True => @lem5353865)). Qed.
Lemma lem5353868 : term381 = True.
Proof. exact (EQ_MP (@lem5353867) (@lem5353865)). Qed.
Lemma lem5353869 : term380 = True.
Proof. exact (TRANS (@lem5353864) (@lem5353868)). Qed.
Lemma lem5353870 : term586 = True.
Proof. exact (TRANS (@lem5353861) (@lem5353869)). Qed.
Lemma lem5353871 : term583 = True.
Proof. exact (TRANS (@lem5353847) (@lem5353870)). Qed.
Lemma lem5353872 : term380 = True.
Proof. exact (TRANS (@lem5353824) (@lem5353871)). Qed.
Lemma lem5353873 : term580 = True.
Proof. exact (TRANS (@lem5353815) (@lem5353872)). Qed.
Lemma lem5353874 : True = term580.
Proof. exact (SYM (@lem5353873)). Qed.
Lemma lem5353875 : term580.
Proof. exact (EQ_MP (@lem5353874) (@lem0)). Qed.
Lemma lem5353876 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term594 _69724 _69726.
Proof. exact (conj (@lem5353875) (@lem5353738 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353878 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5353879 (_69724 : int) (_69726 : int) : term595 _69724 _69726.
Proof. exact (@lem5353878 term267 (term336 _69724 _69726)). Qed.
Lemma lem5353880 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term596 _69724 _69726.
Proof. exact (@lem5353879 _69724 _69726 (@lem5353876 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353881 (_69724 : int) (_69726 : int) : (term597 _69724 _69726) = (term336 _69724 _69726).
Proof. exact (@lem1982733 (term336 _69724 _69726)). Qed.
Lemma lem5353882 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5353883 (_69724 : int) (_69726 : int) : (term598 _69724 _69726) = (term339 _69724 _69726).
Proof. exact (MK_COMB (@lem5353882) (@lem5353881 _69724 _69726)). Qed.
Lemma lem5353884 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5353885 (_69724 : int) (_69726 : int) : (term596 _69724 _69726) = (term340 _69724 _69726).
Proof. exact (MK_COMB (@lem5353883 _69724 _69726) (@lem5353884)). Qed.
Lemma lem5353886 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term340 _69724 _69726.
Proof. exact (EQ_MP (@lem5353885 _69724 _69726) (@lem5353880 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353887 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term599 _69724 _69726.
Proof. exact (conj (@lem5353886 _69724 _69725 _69726 h1) (@lem5353812 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353889 (x : real) (y : real) : term600 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5353890 (_69724 : int) (_69726 : int) : term601 _69724 _69726.
Proof. exact (@lem5353889 (term336 _69724 _69726) (term357 _69724 _69726)). Qed.
Lemma lem5353891 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term602 _69724 _69726.
Proof. exact (@lem5353890 _69724 _69726 (@lem5353887 _69724 _69725 _69726 h1)). Qed.
Lemma lem5353892 (_69724 : int) (_69726 : int) : (term603 _69724 _69726) = (term604 _69724 _69726).
Proof. exact (@lem1982753 (term337 _69724) (real_of_int _69724) (real_of_int _69726) (term356 _69726)). Qed.
Lemma lem5353893 (_69724 : int) : (term605 _69724) = (term606 _69724).
Proof. exact (@lem1982713 term312 (real_of_int _69724)). Qed.
Lemma lem5353895 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5353896 : term267 = term346.
Proof. exact (@lem5353895 term146). Qed.
Lemma lem5353898 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5353899 : term312 = term313.
Proof. exact (@lem5353898 term146). Qed.
Lemma lem5353900 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5353901 : term607 = term608.
Proof. exact (MK_COMB (@lem5353900) (@lem5353899)). Qed.
Lemma lem5353902 : term609 = term610.
Proof. exact (MK_COMB (@lem5353901) (@lem5353896)). Qed.
Lemma lem5353903 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5353905 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5353906 : term380 = term381.
Proof. exact (@lem5353905 (NUMERAL 0) term146). Qed.
Lemma lem5353907 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5353908 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5353909 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5353908 h1) (fun h1 : term381 = True => @lem5353907)). Qed.
Lemma lem5353910 : term381 = True.
Proof. exact (EQ_MP (@lem5353909) (@lem5353907)). Qed.
Lemma lem5353911 : term380 = True.
Proof. exact (TRANS (@lem5353906) (@lem5353910)). Qed.
Lemma lem5353912 : True = term380.
Proof. exact (SYM (@lem5353911)). Qed.
Lemma lem5353913 : term380.
Proof. exact (EQ_MP (@lem5353912) (@lem0)). Qed.
Lemma lem5353914 : term612.
Proof. exact (@lem5353903 (@lem5353913)). Qed.
Lemma lem5353916 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5353917 : term380 = term381.
Proof. exact (@lem5353916 (NUMERAL 0) term146). Qed.
Lemma lem5353918 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5353919 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5353920 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5353919 h1) (fun h1 : term381 = True => @lem5353918)). Qed.
Lemma lem5353921 : term381 = True.
Proof. exact (EQ_MP (@lem5353920) (@lem5353918)). Qed.
Lemma lem5353922 : term380 = True.
Proof. exact (TRANS (@lem5353917) (@lem5353921)). Qed.
Lemma lem5353923 : True = term380.
Proof. exact (SYM (@lem5353922)). Qed.
Lemma lem5353924 : term380.
Proof. exact (EQ_MP (@lem5353923) (@lem0)). Qed.
Lemma lem5353925 : term613.
Proof. exact (@lem5353914 (@lem5353924)). Qed.
Lemma lem5353927 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5353928 : term380 = term381.
Proof. exact (@lem5353927 (NUMERAL 0) term146). Qed.
Lemma lem5353929 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5353930 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5353931 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5353930 h1) (fun h1 : term381 = True => @lem5353929)). Qed.
Lemma lem5353932 : term381 = True.
Proof. exact (EQ_MP (@lem5353931) (@lem5353929)). Qed.
Lemma lem5353933 : term380 = True.
Proof. exact (TRANS (@lem5353928) (@lem5353932)). Qed.
Lemma lem5353934 : True = term380.
Proof. exact (SYM (@lem5353933)). Qed.
Lemma lem5353935 : term380.
Proof. exact (EQ_MP (@lem5353934) (@lem0)). Qed.
Lemma lem5353936 : term614.
Proof. exact (@lem5353925 (@lem5353935)). Qed.
Lemma lem5353938 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5353939 : term321 = term322.
Proof. exact (@lem5353938 term146 term146). Qed.
Lemma lem5353940 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353941 : term324 = term146.
Proof. exact (EQ_MP (@lem5353940) (@lem940073)). Qed.
Lemma lem5353942 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353943 : term322 = term267.
Proof. exact (MK_COMB (@lem5353942) (@lem5353941)). Qed.
Lemma lem5353944 : term321 = term267.
Proof. exact (TRANS (@lem5353939) (@lem5353943)). Qed.
Lemma lem5353946 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5353947 : term347 = term352.
Proof. exact (@lem5353946 term146 term146). Qed.
Lemma lem5353948 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353949 : term324 = term146.
Proof. exact (EQ_MP (@lem5353948) (@lem940073)). Qed.
Lemma lem5353950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353951 : term322 = term267.
Proof. exact (MK_COMB (@lem5353950) (@lem5353949)). Qed.
Lemma lem5353952 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5353953 : term352 = term312.
Proof. exact (MK_COMB (@lem5353952) (@lem5353951)). Qed.
Lemma lem5353954 : term347 = term312.
Proof. exact (TRANS (@lem5353947) (@lem5353953)). Qed.
Lemma lem5353955 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5353956 : term615 = term607.
Proof. exact (MK_COMB (@lem5353955) (@lem5353954)). Qed.
Lemma lem5353957 : term616 = term609.
Proof. exact (MK_COMB (@lem5353956) (@lem5353944)). Qed.
Lemma lem5353959 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5353960 : term609 = term254.
Proof. exact (@lem5353959 term146). Qed.
Lemma lem5353961 : term616 = term254.
Proof. exact (TRANS (@lem5353957) (@lem5353960)). Qed.
Lemma lem5353962 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5353963 : term618 = term390.
Proof. exact (MK_COMB (@lem5353962) (@lem5353961)). Qed.
Lemma lem5353964 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5353965 : term619 = term392.
Proof. exact (MK_COMB (@lem5353963) (@lem5353964)). Qed.
Lemma lem5353967 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5353968 : term392 = term254.
Proof. exact (@lem5353967 term146). Qed.
Lemma lem5353969 : term619 = term254.
Proof. exact (TRANS (@lem5353965) (@lem5353968)). Qed.
Lemma lem5353971 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5353972 : term321 = term322.
Proof. exact (@lem5353971 term146 term146). Qed.
Lemma lem5353973 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5353974 : term324 = term146.
Proof. exact (EQ_MP (@lem5353973) (@lem940073)). Qed.
Lemma lem5353975 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5353976 : term322 = term267.
Proof. exact (MK_COMB (@lem5353975) (@lem5353974)). Qed.
Lemma lem5353977 : term321 = term267.
Proof. exact (TRANS (@lem5353972) (@lem5353976)). Qed.
Lemma lem5353978 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5353979 : term394 = term392.
Proof. exact (MK_COMB (@lem5353978) (@lem5353977)). Qed.
Lemma lem5353981 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5353982 : term392 = term254.
Proof. exact (@lem5353981 term146). Qed.
Lemma lem5353983 : term394 = term254.
Proof. exact (TRANS (@lem5353979) (@lem5353982)). Qed.
Lemma lem5353984 : term254 = term394.
Proof. exact (SYM (@lem5353983)). Qed.
Lemma lem5353985 : term619 = term394.
Proof. exact (TRANS (@lem5353969) (@lem5353984)). Qed.
Lemma lem5353986 : term610 = term309.
Proof. exact (@lem5353936 (@lem5353985)). Qed.
Lemma lem5353987 : term609 = term309.
Proof. exact (TRANS (@lem5353902) (@lem5353986)). Qed.
Lemma lem5353989 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5353990 : term309 = term254.
Proof. exact (@lem5353989 term254). Qed.
Lemma lem5353991 : term609 = term254.
Proof. exact (TRANS (@lem5353987) (@lem5353990)). Qed.
Lemma lem5353992 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5353993 : term620 = term390.
Proof. exact (MK_COMB (@lem5353992) (@lem5353991)). Qed.
Lemma lem5353994 (_69724 : int) : (real_of_int _69724) = (real_of_int _69724).
Proof. exact (eq_refl (real_of_int _69724)). Qed.
Lemma lem5353995 (_69724 : int) : (term606 _69724) = (term621 _69724).
Proof. exact (MK_COMB (@lem5353993) (@lem5353994 _69724)). Qed.
Lemma lem5353996 (_69724 : int) : (term605 _69724) = (term621 _69724).
Proof. exact (TRANS (@lem5353893 _69724) (@lem5353995 _69724)). Qed.
Lemma lem5353997 (_69724 : int) : (term621 _69724) = term254.
Proof. exact (@lem1982719 (real_of_int _69724)). Qed.
Lemma lem5353998 (_69724 : int) : (term605 _69724) = term254.
Proof. exact (TRANS (@lem5353996 _69724) (@lem5353997 _69724)). Qed.
Lemma lem5353999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354000 (_69724 : int) : (term622 _69724) = term623.
Proof. exact (MK_COMB (@lem5353999) (@lem5353998 _69724)). Qed.
Lemma lem5354001 (_69726 : int) : (term624 _69726) = (term625 _69726).
Proof. exact (@lem1982763 (real_of_int _69726) (term337 _69726) term312). Qed.
Lemma lem5354002 (_69726 : int) : (term626 _69726) = (term606 _69726).
Proof. exact (@lem1982715 term312 (real_of_int _69726)). Qed.
Lemma lem5354004 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354005 : term267 = term346.
Proof. exact (@lem5354004 term146). Qed.
Lemma lem5354007 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5354008 : term312 = term313.
Proof. exact (@lem5354007 term146). Qed.
Lemma lem5354009 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354010 : term607 = term608.
Proof. exact (MK_COMB (@lem5354009) (@lem5354008)). Qed.
Lemma lem5354011 : term609 = term610.
Proof. exact (MK_COMB (@lem5354010) (@lem5354005)). Qed.
Lemma lem5354012 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5354014 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354015 : term380 = term381.
Proof. exact (@lem5354014 (NUMERAL 0) term146). Qed.
Lemma lem5354016 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354017 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354018 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354017 h1) (fun h1 : term381 = True => @lem5354016)). Qed.
Lemma lem5354019 : term381 = True.
Proof. exact (EQ_MP (@lem5354018) (@lem5354016)). Qed.
Lemma lem5354020 : term380 = True.
Proof. exact (TRANS (@lem5354015) (@lem5354019)). Qed.
Lemma lem5354021 : True = term380.
Proof. exact (SYM (@lem5354020)). Qed.
Lemma lem5354022 : term380.
Proof. exact (EQ_MP (@lem5354021) (@lem0)). Qed.
Lemma lem5354023 : term612.
Proof. exact (@lem5354012 (@lem5354022)). Qed.
Lemma lem5354025 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354026 : term380 = term381.
Proof. exact (@lem5354025 (NUMERAL 0) term146). Qed.
Lemma lem5354027 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354028 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354029 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354028 h1) (fun h1 : term381 = True => @lem5354027)). Qed.
Lemma lem5354030 : term381 = True.
Proof. exact (EQ_MP (@lem5354029) (@lem5354027)). Qed.
Lemma lem5354031 : term380 = True.
Proof. exact (TRANS (@lem5354026) (@lem5354030)). Qed.
Lemma lem5354032 : True = term380.
Proof. exact (SYM (@lem5354031)). Qed.
Lemma lem5354033 : term380.
Proof. exact (EQ_MP (@lem5354032) (@lem0)). Qed.
Lemma lem5354034 : term613.
Proof. exact (@lem5354023 (@lem5354033)). Qed.
Lemma lem5354036 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354037 : term380 = term381.
Proof. exact (@lem5354036 (NUMERAL 0) term146). Qed.
Lemma lem5354038 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354039 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354040 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354039 h1) (fun h1 : term381 = True => @lem5354038)). Qed.
Lemma lem5354041 : term381 = True.
Proof. exact (EQ_MP (@lem5354040) (@lem5354038)). Qed.
Lemma lem5354042 : term380 = True.
Proof. exact (TRANS (@lem5354037) (@lem5354041)). Qed.
Lemma lem5354043 : True = term380.
Proof. exact (SYM (@lem5354042)). Qed.
Lemma lem5354044 : term380.
Proof. exact (EQ_MP (@lem5354043) (@lem0)). Qed.
Lemma lem5354045 : term614.
Proof. exact (@lem5354034 (@lem5354044)). Qed.
Lemma lem5354047 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354048 : term321 = term322.
Proof. exact (@lem5354047 term146 term146). Qed.
Lemma lem5354049 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354050 : term324 = term146.
Proof. exact (EQ_MP (@lem5354049) (@lem940073)). Qed.
Lemma lem5354051 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354052 : term322 = term267.
Proof. exact (MK_COMB (@lem5354051) (@lem5354050)). Qed.
Lemma lem5354053 : term321 = term267.
Proof. exact (TRANS (@lem5354048) (@lem5354052)). Qed.
Lemma lem5354055 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5354056 : term347 = term352.
Proof. exact (@lem5354055 term146 term146). Qed.
Lemma lem5354057 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354058 : term324 = term146.
Proof. exact (EQ_MP (@lem5354057) (@lem940073)). Qed.
Lemma lem5354059 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354060 : term322 = term267.
Proof. exact (MK_COMB (@lem5354059) (@lem5354058)). Qed.
Lemma lem5354061 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5354062 : term352 = term312.
Proof. exact (MK_COMB (@lem5354061) (@lem5354060)). Qed.
Lemma lem5354063 : term347 = term312.
Proof. exact (TRANS (@lem5354056) (@lem5354062)). Qed.
Lemma lem5354064 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354065 : term615 = term607.
Proof. exact (MK_COMB (@lem5354064) (@lem5354063)). Qed.
Lemma lem5354066 : term616 = term609.
Proof. exact (MK_COMB (@lem5354065) (@lem5354053)). Qed.
Lemma lem5354068 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5354069 : term609 = term254.
Proof. exact (@lem5354068 term146). Qed.
Lemma lem5354070 : term616 = term254.
Proof. exact (TRANS (@lem5354066) (@lem5354069)). Qed.
Lemma lem5354071 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5354072 : term618 = term390.
Proof. exact (MK_COMB (@lem5354071) (@lem5354070)). Qed.
Lemma lem5354073 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5354074 : term619 = term392.
Proof. exact (MK_COMB (@lem5354072) (@lem5354073)). Qed.
Lemma lem5354076 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354077 : term392 = term254.
Proof. exact (@lem5354076 term146). Qed.
Lemma lem5354078 : term619 = term254.
Proof. exact (TRANS (@lem5354074) (@lem5354077)). Qed.
Lemma lem5354080 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354081 : term321 = term322.
Proof. exact (@lem5354080 term146 term146). Qed.
Lemma lem5354082 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354083 : term324 = term146.
Proof. exact (EQ_MP (@lem5354082) (@lem940073)). Qed.
Lemma lem5354084 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354085 : term322 = term267.
Proof. exact (MK_COMB (@lem5354084) (@lem5354083)). Qed.
Lemma lem5354086 : term321 = term267.
Proof. exact (TRANS (@lem5354081) (@lem5354085)). Qed.
Lemma lem5354087 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5354088 : term394 = term392.
Proof. exact (MK_COMB (@lem5354087) (@lem5354086)). Qed.
Lemma lem5354090 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354091 : term392 = term254.
Proof. exact (@lem5354090 term146). Qed.
Lemma lem5354092 : term394 = term254.
Proof. exact (TRANS (@lem5354088) (@lem5354091)). Qed.
Lemma lem5354093 : term254 = term394.
Proof. exact (SYM (@lem5354092)). Qed.
Lemma lem5354094 : term619 = term394.
Proof. exact (TRANS (@lem5354078) (@lem5354093)). Qed.
Lemma lem5354095 : term610 = term309.
Proof. exact (@lem5354045 (@lem5354094)). Qed.
Lemma lem5354096 : term609 = term309.
Proof. exact (TRANS (@lem5354011) (@lem5354095)). Qed.
Lemma lem5354098 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5354099 : term309 = term254.
Proof. exact (@lem5354098 term254). Qed.
Lemma lem5354100 : term609 = term254.
Proof. exact (TRANS (@lem5354096) (@lem5354099)). Qed.
Lemma lem5354101 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5354102 : term620 = term390.
Proof. exact (MK_COMB (@lem5354101) (@lem5354100)). Qed.
Lemma lem5354103 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5354104 (_69726 : int) : (term606 _69726) = (term621 _69726).
Proof. exact (MK_COMB (@lem5354102) (@lem5354103 _69726)). Qed.
Lemma lem5354105 (_69726 : int) : (term626 _69726) = (term621 _69726).
Proof. exact (TRANS (@lem5354002 _69726) (@lem5354104 _69726)). Qed.
Lemma lem5354106 (_69726 : int) : (term621 _69726) = term254.
Proof. exact (@lem1982719 (real_of_int _69726)). Qed.
Lemma lem5354107 (_69726 : int) : (term626 _69726) = term254.
Proof. exact (TRANS (@lem5354105 _69726) (@lem5354106 _69726)). Qed.
Lemma lem5354108 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354109 (_69726 : int) : (term627 _69726) = term623.
Proof. exact (MK_COMB (@lem5354108) (@lem5354107 _69726)). Qed.
Lemma lem5354110 : term312 = term312.
Proof. exact (eq_refl term312). Qed.
Lemma lem5354111 (_69726 : int) : (term625 _69726) = term628.
Proof. exact (MK_COMB (@lem5354109 _69726) (@lem5354110)). Qed.
Lemma lem5354112 (_69726 : int) : (term624 _69726) = term628.
Proof. exact (TRANS (@lem5354001 _69726) (@lem5354111 _69726)). Qed.
Lemma lem5354113 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5354114 (_69726 : int) : (term624 _69726) = term312.
Proof. exact (TRANS (@lem5354112 _69726) (@lem5354113)). Qed.
Lemma lem5354115 (_69724 : int) (_69726 : int) : (term604 _69724 _69726) = term628.
Proof. exact (MK_COMB (@lem5354000 _69724) (@lem5354114 _69726)). Qed.
Lemma lem5354116 (_69724 : int) (_69726 : int) : (term603 _69724 _69726) = term628.
Proof. exact (TRANS (@lem5353892 _69724 _69726) (@lem5354115 _69724 _69726)). Qed.
Lemma lem5354117 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5354118 (_69724 : int) (_69726 : int) : (term603 _69724 _69726) = term312.
Proof. exact (TRANS (@lem5354116 _69724 _69726) (@lem5354117)). Qed.
Lemma lem5354119 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5354120 (_69724 : int) (_69726 : int) : (term629 _69724 _69726) = term630.
Proof. exact (MK_COMB (@lem5354119) (@lem5354118 _69724 _69726)). Qed.
Lemma lem5354121 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5354122 (_69724 : int) (_69726 : int) : (term602 _69724 _69726) = term631.
Proof. exact (MK_COMB (@lem5354120 _69724 _69726) (@lem5354121)). Qed.
Lemma lem5354123 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : term631.
Proof. exact (EQ_MP (@lem5354122 _69724 _69726) (@lem5353891 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354125 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5354126 : term631 = term632.
Proof. exact (@lem5354125 term254 term312). Qed.
Lemma lem5354128 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5354129 : term312 = term313.
Proof. exact (@lem5354128 term146). Qed.
Lemma lem5354131 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354132 : term254 = term309.
Proof. exact (@lem5354131 (NUMERAL 0)). Qed.
Lemma lem5354133 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5354134 : term256 = term633.
Proof. exact (MK_COMB (@lem5354133) (@lem5354132)). Qed.
Lemma lem5354135 : term632 = term634.
Proof. exact (MK_COMB (@lem5354134) (@lem5354129)). Qed.
Lemma lem5354136 : term635.
Proof. exact (@lem1980026 term254 term267 term312 term267). Qed.
Lemma lem5354138 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354139 : term380 = term381.
Proof. exact (@lem5354138 (NUMERAL 0) term146). Qed.
Lemma lem5354140 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354141 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354142 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354141 h1) (fun h1 : term381 = True => @lem5354140)). Qed.
Lemma lem5354143 : term381 = True.
Proof. exact (EQ_MP (@lem5354142) (@lem5354140)). Qed.
Lemma lem5354144 : term380 = True.
Proof. exact (TRANS (@lem5354139) (@lem5354143)). Qed.
Lemma lem5354145 : True = term380.
Proof. exact (SYM (@lem5354144)). Qed.
Lemma lem5354146 : term380.
Proof. exact (EQ_MP (@lem5354145) (@lem0)). Qed.
Lemma lem5354147 : term636.
Proof. exact (@lem5354136 (@lem5354146)). Qed.
Lemma lem5354149 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354150 : term380 = term381.
Proof. exact (@lem5354149 (NUMERAL 0) term146). Qed.
Lemma lem5354151 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354152 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354153 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354152 h1) (fun h1 : term381 = True => @lem5354151)). Qed.
Lemma lem5354154 : term381 = True.
Proof. exact (EQ_MP (@lem5354153) (@lem5354151)). Qed.
Lemma lem5354155 : term380 = True.
Proof. exact (TRANS (@lem5354150) (@lem5354154)). Qed.
Lemma lem5354156 : True = term380.
Proof. exact (SYM (@lem5354155)). Qed.
Lemma lem5354157 : term380.
Proof. exact (EQ_MP (@lem5354156) (@lem0)). Qed.
Lemma lem5354158 : term634 = term637.
Proof. exact (@lem5354147 (@lem5354157)). Qed.
Lemma lem5354160 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5354161 : term347 = term352.
Proof. exact (@lem5354160 term146 term146). Qed.
Lemma lem5354162 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354163 : term324 = term146.
Proof. exact (EQ_MP (@lem5354162) (@lem940073)). Qed.
Lemma lem5354164 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354165 : term322 = term267.
Proof. exact (MK_COMB (@lem5354164) (@lem5354163)). Qed.
Lemma lem5354166 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5354167 : term352 = term312.
Proof. exact (MK_COMB (@lem5354166) (@lem5354165)). Qed.
Lemma lem5354168 : term347 = term312.
Proof. exact (TRANS (@lem5354161) (@lem5354167)). Qed.
Lemma lem5354170 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354171 : term392 = term254.
Proof. exact (@lem5354170 term146). Qed.
Lemma lem5354172 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5354173 : term638 = term256.
Proof. exact (MK_COMB (@lem5354172) (@lem5354171)). Qed.
Lemma lem5354174 : term637 = term632.
Proof. exact (MK_COMB (@lem5354173) (@lem5354168)). Qed.
Lemma lem5354176 (m : nat) (n : nat) : (term639 m n) = (term640 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5354177 : term632 = term641.
Proof. exact (@lem5354176 (NUMERAL 0) term146). Qed.
Lemma lem5354178 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354179 (h1 : term382 = (BIT1 0)) : (term146 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5354180 : (term382 = (BIT1 0)) = ((term146 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354179 h1) (fun h1 : (term146 = (NUMERAL 0)) = False => @lem5354178)). Qed.
Lemma lem5354181 : (term146 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5354180) (@lem5354178)). Qed.
Lemma lem5354182 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5354183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5354184 : term642 = (and True).
Proof. exact (MK_COMB (@lem5354183) (@lem5354182)). Qed.
Lemma lem5354185 : term641 = (True /\ False).
Proof. exact (MK_COMB (@lem5354184) (@lem5354181)). Qed.
Lemma lem5354187 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5354188 : term641 = False.
Proof. exact (TRANS (@lem5354185) (@lem5354187)). Qed.
Lemma lem5354189 : term632 = False.
Proof. exact (TRANS (@lem5354177) (@lem5354188)). Qed.
Lemma lem5354190 : term637 = False.
Proof. exact (TRANS (@lem5354174) (@lem5354189)). Qed.
Lemma lem5354191 : term634 = False.
Proof. exact (TRANS (@lem5354158) (@lem5354190)). Qed.
Lemma lem5354192 : term632 = False.
Proof. exact (TRANS (@lem5354135) (@lem5354191)). Qed.
Lemma lem5354193 : term631 = False.
Proof. exact (TRANS (@lem5354126) (@lem5354192)). Qed.
Lemma lem5354194 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term579 _69724 _69725 _69726) : False.
Proof. exact (EQ_MP (@lem5354193) (@lem5354123 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354195 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term643 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5354196 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term572 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5354195 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354198 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term541 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5354196 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354200 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term510 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5354198 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354202 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term479 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5354200 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354205 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term449 _69724 _69726.
Proof. exact (proj1 (@lem5354202 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354206 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term398 _69724 _69726.
Proof. exact (proj2 (@lem5354205 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354207 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term363 _69724 _69726.
Proof. exact (proj1 (@lem5354205 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354211 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5354212 : term580 = term380.
Proof. exact (@lem5354211 term254 term267). Qed.
Lemma lem5354214 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354215 : term267 = term346.
Proof. exact (@lem5354214 term146). Qed.
Lemma lem5354217 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354218 : term254 = term309.
Proof. exact (@lem5354217 (NUMERAL 0)). Qed.
Lemma lem5354219 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5354220 : term581 = term582.
Proof. exact (MK_COMB (@lem5354219) (@lem5354218)). Qed.
Lemma lem5354221 : term380 = term583.
Proof. exact (MK_COMB (@lem5354220) (@lem5354215)). Qed.
Lemma lem5354222 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5354224 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354225 : term380 = term381.
Proof. exact (@lem5354224 (NUMERAL 0) term146). Qed.
Lemma lem5354226 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354227 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354228 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354227 h1) (fun h1 : term381 = True => @lem5354226)). Qed.
Lemma lem5354229 : term381 = True.
Proof. exact (EQ_MP (@lem5354228) (@lem5354226)). Qed.
Lemma lem5354230 : term380 = True.
Proof. exact (TRANS (@lem5354225) (@lem5354229)). Qed.
Lemma lem5354231 : True = term380.
Proof. exact (SYM (@lem5354230)). Qed.
Lemma lem5354232 : term380.
Proof. exact (EQ_MP (@lem5354231) (@lem0)). Qed.
Lemma lem5354233 : term585.
Proof. exact (@lem5354222 (@lem5354232)). Qed.
Lemma lem5354235 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354236 : term380 = term381.
Proof. exact (@lem5354235 (NUMERAL 0) term146). Qed.
Lemma lem5354237 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354238 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354239 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354238 h1) (fun h1 : term381 = True => @lem5354237)). Qed.
Lemma lem5354240 : term381 = True.
Proof. exact (EQ_MP (@lem5354239) (@lem5354237)). Qed.
Lemma lem5354241 : term380 = True.
Proof. exact (TRANS (@lem5354236) (@lem5354240)). Qed.
Lemma lem5354242 : True = term380.
Proof. exact (SYM (@lem5354241)). Qed.
Lemma lem5354243 : term380.
Proof. exact (EQ_MP (@lem5354242) (@lem0)). Qed.
Lemma lem5354244 : term583 = term586.
Proof. exact (@lem5354233 (@lem5354243)). Qed.
Lemma lem5354246 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354247 : term321 = term322.
Proof. exact (@lem5354246 term146 term146). Qed.
Lemma lem5354248 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354249 : term324 = term146.
Proof. exact (EQ_MP (@lem5354248) (@lem940073)). Qed.
Lemma lem5354250 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354251 : term322 = term267.
Proof. exact (MK_COMB (@lem5354250) (@lem5354249)). Qed.
Lemma lem5354252 : term321 = term267.
Proof. exact (TRANS (@lem5354247) (@lem5354251)). Qed.
Lemma lem5354254 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354255 : term392 = term254.
Proof. exact (@lem5354254 term146). Qed.
Lemma lem5354256 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5354257 : term587 = term581.
Proof. exact (MK_COMB (@lem5354256) (@lem5354255)). Qed.
Lemma lem5354258 : term586 = term380.
Proof. exact (MK_COMB (@lem5354257) (@lem5354252)). Qed.
Lemma lem5354260 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354261 : term380 = term381.
Proof. exact (@lem5354260 (NUMERAL 0) term146). Qed.
Lemma lem5354262 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354263 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354264 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354263 h1) (fun h1 : term381 = True => @lem5354262)). Qed.
Lemma lem5354265 : term381 = True.
Proof. exact (EQ_MP (@lem5354264) (@lem5354262)). Qed.
Lemma lem5354266 : term380 = True.
Proof. exact (TRANS (@lem5354261) (@lem5354265)). Qed.
Lemma lem5354267 : term586 = True.
Proof. exact (TRANS (@lem5354258) (@lem5354266)). Qed.
Lemma lem5354268 : term583 = True.
Proof. exact (TRANS (@lem5354244) (@lem5354267)). Qed.
Lemma lem5354269 : term380 = True.
Proof. exact (TRANS (@lem5354221) (@lem5354268)). Qed.
Lemma lem5354270 : term580 = True.
Proof. exact (TRANS (@lem5354212) (@lem5354269)). Qed.
Lemma lem5354271 : True = term580.
Proof. exact (SYM (@lem5354270)). Qed.
Lemma lem5354272 : term580.
Proof. exact (EQ_MP (@lem5354271) (@lem0)). Qed.
Lemma lem5354273 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term644 _69724 _69726.
Proof. exact (conj (@lem5354272) (@lem5354207 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354275 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5354276 (_69724 : int) (_69726 : int) : term645 _69724 _69726.
Proof. exact (@lem5354275 term267 (term361 _69724 _69726)). Qed.
Lemma lem5354277 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term646 _69724 _69726.
Proof. exact (@lem5354276 _69724 _69726 (@lem5354273 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354278 (_69724 : int) (_69726 : int) : (term647 _69724 _69726) = (term361 _69724 _69726).
Proof. exact (@lem1982733 (term361 _69724 _69726)). Qed.
Lemma lem5354279 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5354280 (_69724 : int) (_69726 : int) : (term648 _69724 _69726) = (term362 _69724 _69726).
Proof. exact (MK_COMB (@lem5354279) (@lem5354278 _69724 _69726)). Qed.
Lemma lem5354281 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5354282 (_69724 : int) (_69726 : int) : (term646 _69724 _69726) = (term363 _69724 _69726).
Proof. exact (MK_COMB (@lem5354280 _69724 _69726) (@lem5354281)). Qed.
Lemma lem5354283 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term363 _69724 _69726.
Proof. exact (EQ_MP (@lem5354282 _69724 _69726) (@lem5354277 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354285 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5354286 : term580 = term380.
Proof. exact (@lem5354285 term254 term267). Qed.
Lemma lem5354288 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354289 : term267 = term346.
Proof. exact (@lem5354288 term146). Qed.
Lemma lem5354291 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354292 : term254 = term309.
Proof. exact (@lem5354291 (NUMERAL 0)). Qed.
Lemma lem5354293 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5354294 : term581 = term582.
Proof. exact (MK_COMB (@lem5354293) (@lem5354292)). Qed.
Lemma lem5354295 : term380 = term583.
Proof. exact (MK_COMB (@lem5354294) (@lem5354289)). Qed.
Lemma lem5354296 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5354298 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354299 : term380 = term381.
Proof. exact (@lem5354298 (NUMERAL 0) term146). Qed.
Lemma lem5354300 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354301 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354302 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354301 h1) (fun h1 : term381 = True => @lem5354300)). Qed.
Lemma lem5354303 : term381 = True.
Proof. exact (EQ_MP (@lem5354302) (@lem5354300)). Qed.
Lemma lem5354304 : term380 = True.
Proof. exact (TRANS (@lem5354299) (@lem5354303)). Qed.
Lemma lem5354305 : True = term380.
Proof. exact (SYM (@lem5354304)). Qed.
Lemma lem5354306 : term380.
Proof. exact (EQ_MP (@lem5354305) (@lem0)). Qed.
Lemma lem5354307 : term585.
Proof. exact (@lem5354296 (@lem5354306)). Qed.
Lemma lem5354309 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354310 : term380 = term381.
Proof. exact (@lem5354309 (NUMERAL 0) term146). Qed.
Lemma lem5354311 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354312 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354313 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354312 h1) (fun h1 : term381 = True => @lem5354311)). Qed.
Lemma lem5354314 : term381 = True.
Proof. exact (EQ_MP (@lem5354313) (@lem5354311)). Qed.
Lemma lem5354315 : term380 = True.
Proof. exact (TRANS (@lem5354310) (@lem5354314)). Qed.
Lemma lem5354316 : True = term380.
Proof. exact (SYM (@lem5354315)). Qed.
Lemma lem5354317 : term380.
Proof. exact (EQ_MP (@lem5354316) (@lem0)). Qed.
Lemma lem5354318 : term583 = term586.
Proof. exact (@lem5354307 (@lem5354317)). Qed.
Lemma lem5354320 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354321 : term321 = term322.
Proof. exact (@lem5354320 term146 term146). Qed.
Lemma lem5354322 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354323 : term324 = term146.
Proof. exact (EQ_MP (@lem5354322) (@lem940073)). Qed.
Lemma lem5354324 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354325 : term322 = term267.
Proof. exact (MK_COMB (@lem5354324) (@lem5354323)). Qed.
Lemma lem5354326 : term321 = term267.
Proof. exact (TRANS (@lem5354321) (@lem5354325)). Qed.
Lemma lem5354328 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354329 : term392 = term254.
Proof. exact (@lem5354328 term146). Qed.
Lemma lem5354330 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5354331 : term587 = term581.
Proof. exact (MK_COMB (@lem5354330) (@lem5354329)). Qed.
Lemma lem5354332 : term586 = term380.
Proof. exact (MK_COMB (@lem5354331) (@lem5354326)). Qed.
Lemma lem5354334 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354335 : term380 = term381.
Proof. exact (@lem5354334 (NUMERAL 0) term146). Qed.
Lemma lem5354336 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354337 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354338 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354337 h1) (fun h1 : term381 = True => @lem5354336)). Qed.
Lemma lem5354339 : term381 = True.
Proof. exact (EQ_MP (@lem5354338) (@lem5354336)). Qed.
Lemma lem5354340 : term380 = True.
Proof. exact (TRANS (@lem5354335) (@lem5354339)). Qed.
Lemma lem5354341 : term586 = True.
Proof. exact (TRANS (@lem5354332) (@lem5354340)). Qed.
Lemma lem5354342 : term583 = True.
Proof. exact (TRANS (@lem5354318) (@lem5354341)). Qed.
Lemma lem5354343 : term380 = True.
Proof. exact (TRANS (@lem5354295) (@lem5354342)). Qed.
Lemma lem5354344 : term580 = True.
Proof. exact (TRANS (@lem5354286) (@lem5354343)). Qed.
Lemma lem5354345 : True = term580.
Proof. exact (SYM (@lem5354344)). Qed.
Lemma lem5354346 : term580.
Proof. exact (EQ_MP (@lem5354345) (@lem0)). Qed.
Lemma lem5354347 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term649 _69724 _69726.
Proof. exact (conj (@lem5354346) (@lem5354206 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354349 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5354350 (_69724 : int) (_69726 : int) : term650 _69724 _69726.
Proof. exact (@lem5354349 term267 (term335 _69724 _69726)). Qed.
Lemma lem5354351 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term651 _69724 _69726.
Proof. exact (@lem5354350 _69724 _69726 (@lem5354347 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354352 (_69724 : int) (_69726 : int) : (term652 _69724 _69726) = (term335 _69724 _69726).
Proof. exact (@lem1982733 (term335 _69724 _69726)). Qed.
Lemma lem5354353 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5354354 (_69724 : int) (_69726 : int) : (term653 _69724 _69726) = (term397 _69724 _69726).
Proof. exact (MK_COMB (@lem5354353) (@lem5354352 _69724 _69726)). Qed.
Lemma lem5354355 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5354356 (_69724 : int) (_69726 : int) : (term651 _69724 _69726) = (term398 _69724 _69726).
Proof. exact (MK_COMB (@lem5354354 _69724 _69726) (@lem5354355)). Qed.
Lemma lem5354357 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term398 _69724 _69726.
Proof. exact (EQ_MP (@lem5354356 _69724 _69726) (@lem5354351 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354358 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term654 _69724 _69726.
Proof. exact (conj (@lem5354357 _69724 _69725 _69726 h1) (@lem5354283 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354360 (x : real) (y : real) : term600 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5354361 (_69724 : int) (_69726 : int) : term655 _69724 _69726.
Proof. exact (@lem5354360 (term335 _69724 _69726) (term361 _69724 _69726)). Qed.
Lemma lem5354362 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term656 _69724 _69726.
Proof. exact (@lem5354361 _69724 _69726 (@lem5354358 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354363 (_69724 : int) (_69726 : int) : (term657 _69724 _69726) = (term658 _69724 _69726).
Proof. exact (@lem1982753 (real_of_int _69724) (term337 _69724) (term337 _69726) (term659 _69726)). Qed.
Lemma lem5354364 (_69724 : int) : (term626 _69724) = (term606 _69724).
Proof. exact (@lem1982715 term312 (real_of_int _69724)). Qed.
Lemma lem5354366 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354367 : term267 = term346.
Proof. exact (@lem5354366 term146). Qed.
Lemma lem5354369 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5354370 : term312 = term313.
Proof. exact (@lem5354369 term146). Qed.
Lemma lem5354371 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354372 : term607 = term608.
Proof. exact (MK_COMB (@lem5354371) (@lem5354370)). Qed.
Lemma lem5354373 : term609 = term610.
Proof. exact (MK_COMB (@lem5354372) (@lem5354367)). Qed.
Lemma lem5354374 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5354376 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354377 : term380 = term381.
Proof. exact (@lem5354376 (NUMERAL 0) term146). Qed.
Lemma lem5354378 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354379 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354380 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354379 h1) (fun h1 : term381 = True => @lem5354378)). Qed.
Lemma lem5354381 : term381 = True.
Proof. exact (EQ_MP (@lem5354380) (@lem5354378)). Qed.
Lemma lem5354382 : term380 = True.
Proof. exact (TRANS (@lem5354377) (@lem5354381)). Qed.
Lemma lem5354383 : True = term380.
Proof. exact (SYM (@lem5354382)). Qed.
Lemma lem5354384 : term380.
Proof. exact (EQ_MP (@lem5354383) (@lem0)). Qed.
Lemma lem5354385 : term612.
Proof. exact (@lem5354374 (@lem5354384)). Qed.
Lemma lem5354387 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354388 : term380 = term381.
Proof. exact (@lem5354387 (NUMERAL 0) term146). Qed.
Lemma lem5354389 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354390 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354391 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354390 h1) (fun h1 : term381 = True => @lem5354389)). Qed.
Lemma lem5354392 : term381 = True.
Proof. exact (EQ_MP (@lem5354391) (@lem5354389)). Qed.
Lemma lem5354393 : term380 = True.
Proof. exact (TRANS (@lem5354388) (@lem5354392)). Qed.
Lemma lem5354394 : True = term380.
Proof. exact (SYM (@lem5354393)). Qed.
Lemma lem5354395 : term380.
Proof. exact (EQ_MP (@lem5354394) (@lem0)). Qed.
Lemma lem5354396 : term613.
Proof. exact (@lem5354385 (@lem5354395)). Qed.
Lemma lem5354398 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354399 : term380 = term381.
Proof. exact (@lem5354398 (NUMERAL 0) term146). Qed.
Lemma lem5354400 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354401 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354402 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354401 h1) (fun h1 : term381 = True => @lem5354400)). Qed.
Lemma lem5354403 : term381 = True.
Proof. exact (EQ_MP (@lem5354402) (@lem5354400)). Qed.
Lemma lem5354404 : term380 = True.
Proof. exact (TRANS (@lem5354399) (@lem5354403)). Qed.
Lemma lem5354405 : True = term380.
Proof. exact (SYM (@lem5354404)). Qed.
Lemma lem5354406 : term380.
Proof. exact (EQ_MP (@lem5354405) (@lem0)). Qed.
Lemma lem5354407 : term614.
Proof. exact (@lem5354396 (@lem5354406)). Qed.
Lemma lem5354409 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354410 : term321 = term322.
Proof. exact (@lem5354409 term146 term146). Qed.
Lemma lem5354411 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354412 : term324 = term146.
Proof. exact (EQ_MP (@lem5354411) (@lem940073)). Qed.
Lemma lem5354413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354414 : term322 = term267.
Proof. exact (MK_COMB (@lem5354413) (@lem5354412)). Qed.
Lemma lem5354415 : term321 = term267.
Proof. exact (TRANS (@lem5354410) (@lem5354414)). Qed.
Lemma lem5354417 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5354418 : term347 = term352.
Proof. exact (@lem5354417 term146 term146). Qed.
Lemma lem5354419 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354420 : term324 = term146.
Proof. exact (EQ_MP (@lem5354419) (@lem940073)). Qed.
Lemma lem5354421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354422 : term322 = term267.
Proof. exact (MK_COMB (@lem5354421) (@lem5354420)). Qed.
Lemma lem5354423 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5354424 : term352 = term312.
Proof. exact (MK_COMB (@lem5354423) (@lem5354422)). Qed.
Lemma lem5354425 : term347 = term312.
Proof. exact (TRANS (@lem5354418) (@lem5354424)). Qed.
Lemma lem5354426 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354427 : term615 = term607.
Proof. exact (MK_COMB (@lem5354426) (@lem5354425)). Qed.
Lemma lem5354428 : term616 = term609.
Proof. exact (MK_COMB (@lem5354427) (@lem5354415)). Qed.
Lemma lem5354430 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5354431 : term609 = term254.
Proof. exact (@lem5354430 term146). Qed.
Lemma lem5354432 : term616 = term254.
Proof. exact (TRANS (@lem5354428) (@lem5354431)). Qed.
Lemma lem5354433 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5354434 : term618 = term390.
Proof. exact (MK_COMB (@lem5354433) (@lem5354432)). Qed.
Lemma lem5354435 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5354436 : term619 = term392.
Proof. exact (MK_COMB (@lem5354434) (@lem5354435)). Qed.
Lemma lem5354438 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354439 : term392 = term254.
Proof. exact (@lem5354438 term146). Qed.
Lemma lem5354440 : term619 = term254.
Proof. exact (TRANS (@lem5354436) (@lem5354439)). Qed.
Lemma lem5354442 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354443 : term321 = term322.
Proof. exact (@lem5354442 term146 term146). Qed.
Lemma lem5354444 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354445 : term324 = term146.
Proof. exact (EQ_MP (@lem5354444) (@lem940073)). Qed.
Lemma lem5354446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354447 : term322 = term267.
Proof. exact (MK_COMB (@lem5354446) (@lem5354445)). Qed.
Lemma lem5354448 : term321 = term267.
Proof. exact (TRANS (@lem5354443) (@lem5354447)). Qed.
Lemma lem5354449 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5354450 : term394 = term392.
Proof. exact (MK_COMB (@lem5354449) (@lem5354448)). Qed.
Lemma lem5354452 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354453 : term392 = term254.
Proof. exact (@lem5354452 term146). Qed.
Lemma lem5354454 : term394 = term254.
Proof. exact (TRANS (@lem5354450) (@lem5354453)). Qed.
Lemma lem5354455 : term254 = term394.
Proof. exact (SYM (@lem5354454)). Qed.
Lemma lem5354456 : term619 = term394.
Proof. exact (TRANS (@lem5354440) (@lem5354455)). Qed.
Lemma lem5354457 : term610 = term309.
Proof. exact (@lem5354407 (@lem5354456)). Qed.
Lemma lem5354458 : term609 = term309.
Proof. exact (TRANS (@lem5354373) (@lem5354457)). Qed.
Lemma lem5354460 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5354461 : term309 = term254.
Proof. exact (@lem5354460 term254). Qed.
Lemma lem5354462 : term609 = term254.
Proof. exact (TRANS (@lem5354458) (@lem5354461)). Qed.
Lemma lem5354463 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5354464 : term620 = term390.
Proof. exact (MK_COMB (@lem5354463) (@lem5354462)). Qed.
Lemma lem5354465 (_69724 : int) : (real_of_int _69724) = (real_of_int _69724).
Proof. exact (eq_refl (real_of_int _69724)). Qed.
Lemma lem5354466 (_69724 : int) : (term606 _69724) = (term621 _69724).
Proof. exact (MK_COMB (@lem5354464) (@lem5354465 _69724)). Qed.
Lemma lem5354467 (_69724 : int) : (term626 _69724) = (term621 _69724).
Proof. exact (TRANS (@lem5354364 _69724) (@lem5354466 _69724)). Qed.
Lemma lem5354468 (_69724 : int) : (term621 _69724) = term254.
Proof. exact (@lem1982719 (real_of_int _69724)). Qed.
Lemma lem5354469 (_69724 : int) : (term626 _69724) = term254.
Proof. exact (TRANS (@lem5354467 _69724) (@lem5354468 _69724)). Qed.
Lemma lem5354470 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354471 (_69724 : int) : (term627 _69724) = term623.
Proof. exact (MK_COMB (@lem5354470) (@lem5354469 _69724)). Qed.
Lemma lem5354472 (_69726 : int) : (term660 _69726) = (term661 _69726).
Proof. exact (@lem1982763 (term337 _69726) (real_of_int _69726) term312). Qed.
Lemma lem5354473 (_69726 : int) : (term605 _69726) = (term606 _69726).
Proof. exact (@lem1982713 term312 (real_of_int _69726)). Qed.
Lemma lem5354475 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354476 : term267 = term346.
Proof. exact (@lem5354475 term146). Qed.
Lemma lem5354478 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5354479 : term312 = term313.
Proof. exact (@lem5354478 term146). Qed.
Lemma lem5354480 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354481 : term607 = term608.
Proof. exact (MK_COMB (@lem5354480) (@lem5354479)). Qed.
Lemma lem5354482 : term609 = term610.
Proof. exact (MK_COMB (@lem5354481) (@lem5354476)). Qed.
Lemma lem5354483 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5354485 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354486 : term380 = term381.
Proof. exact (@lem5354485 (NUMERAL 0) term146). Qed.
Lemma lem5354487 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354488 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354489 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354488 h1) (fun h1 : term381 = True => @lem5354487)). Qed.
Lemma lem5354490 : term381 = True.
Proof. exact (EQ_MP (@lem5354489) (@lem5354487)). Qed.
Lemma lem5354491 : term380 = True.
Proof. exact (TRANS (@lem5354486) (@lem5354490)). Qed.
Lemma lem5354492 : True = term380.
Proof. exact (SYM (@lem5354491)). Qed.
Lemma lem5354493 : term380.
Proof. exact (EQ_MP (@lem5354492) (@lem0)). Qed.
Lemma lem5354494 : term612.
Proof. exact (@lem5354483 (@lem5354493)). Qed.
Lemma lem5354496 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354497 : term380 = term381.
Proof. exact (@lem5354496 (NUMERAL 0) term146). Qed.
Lemma lem5354498 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354499 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354500 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354499 h1) (fun h1 : term381 = True => @lem5354498)). Qed.
Lemma lem5354501 : term381 = True.
Proof. exact (EQ_MP (@lem5354500) (@lem5354498)). Qed.
Lemma lem5354502 : term380 = True.
Proof. exact (TRANS (@lem5354497) (@lem5354501)). Qed.
Lemma lem5354503 : True = term380.
Proof. exact (SYM (@lem5354502)). Qed.
Lemma lem5354504 : term380.
Proof. exact (EQ_MP (@lem5354503) (@lem0)). Qed.
Lemma lem5354505 : term613.
Proof. exact (@lem5354494 (@lem5354504)). Qed.
Lemma lem5354507 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354508 : term380 = term381.
Proof. exact (@lem5354507 (NUMERAL 0) term146). Qed.
Lemma lem5354509 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354510 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354511 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354510 h1) (fun h1 : term381 = True => @lem5354509)). Qed.
Lemma lem5354512 : term381 = True.
Proof. exact (EQ_MP (@lem5354511) (@lem5354509)). Qed.
Lemma lem5354513 : term380 = True.
Proof. exact (TRANS (@lem5354508) (@lem5354512)). Qed.
Lemma lem5354514 : True = term380.
Proof. exact (SYM (@lem5354513)). Qed.
Lemma lem5354515 : term380.
Proof. exact (EQ_MP (@lem5354514) (@lem0)). Qed.
Lemma lem5354516 : term614.
Proof. exact (@lem5354505 (@lem5354515)). Qed.
Lemma lem5354518 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354519 : term321 = term322.
Proof. exact (@lem5354518 term146 term146). Qed.
Lemma lem5354520 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354521 : term324 = term146.
Proof. exact (EQ_MP (@lem5354520) (@lem940073)). Qed.
Lemma lem5354522 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354523 : term322 = term267.
Proof. exact (MK_COMB (@lem5354522) (@lem5354521)). Qed.
Lemma lem5354524 : term321 = term267.
Proof. exact (TRANS (@lem5354519) (@lem5354523)). Qed.
Lemma lem5354526 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5354527 : term347 = term352.
Proof. exact (@lem5354526 term146 term146). Qed.
Lemma lem5354528 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354529 : term324 = term146.
Proof. exact (EQ_MP (@lem5354528) (@lem940073)). Qed.
Lemma lem5354530 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354531 : term322 = term267.
Proof. exact (MK_COMB (@lem5354530) (@lem5354529)). Qed.
Lemma lem5354532 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5354533 : term352 = term312.
Proof. exact (MK_COMB (@lem5354532) (@lem5354531)). Qed.
Lemma lem5354534 : term347 = term312.
Proof. exact (TRANS (@lem5354527) (@lem5354533)). Qed.
Lemma lem5354535 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354536 : term615 = term607.
Proof. exact (MK_COMB (@lem5354535) (@lem5354534)). Qed.
Lemma lem5354537 : term616 = term609.
Proof. exact (MK_COMB (@lem5354536) (@lem5354524)). Qed.
Lemma lem5354539 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5354540 : term609 = term254.
Proof. exact (@lem5354539 term146). Qed.
Lemma lem5354541 : term616 = term254.
Proof. exact (TRANS (@lem5354537) (@lem5354540)). Qed.
Lemma lem5354542 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5354543 : term618 = term390.
Proof. exact (MK_COMB (@lem5354542) (@lem5354541)). Qed.
Lemma lem5354544 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5354545 : term619 = term392.
Proof. exact (MK_COMB (@lem5354543) (@lem5354544)). Qed.
Lemma lem5354547 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354548 : term392 = term254.
Proof. exact (@lem5354547 term146). Qed.
Lemma lem5354549 : term619 = term254.
Proof. exact (TRANS (@lem5354545) (@lem5354548)). Qed.
Lemma lem5354551 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354552 : term321 = term322.
Proof. exact (@lem5354551 term146 term146). Qed.
Lemma lem5354553 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354554 : term324 = term146.
Proof. exact (EQ_MP (@lem5354553) (@lem940073)). Qed.
Lemma lem5354555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354556 : term322 = term267.
Proof. exact (MK_COMB (@lem5354555) (@lem5354554)). Qed.
Lemma lem5354557 : term321 = term267.
Proof. exact (TRANS (@lem5354552) (@lem5354556)). Qed.
Lemma lem5354558 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5354559 : term394 = term392.
Proof. exact (MK_COMB (@lem5354558) (@lem5354557)). Qed.
Lemma lem5354561 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354562 : term392 = term254.
Proof. exact (@lem5354561 term146). Qed.
Lemma lem5354563 : term394 = term254.
Proof. exact (TRANS (@lem5354559) (@lem5354562)). Qed.
Lemma lem5354564 : term254 = term394.
Proof. exact (SYM (@lem5354563)). Qed.
Lemma lem5354565 : term619 = term394.
Proof. exact (TRANS (@lem5354549) (@lem5354564)). Qed.
Lemma lem5354566 : term610 = term309.
Proof. exact (@lem5354516 (@lem5354565)). Qed.
Lemma lem5354567 : term609 = term309.
Proof. exact (TRANS (@lem5354482) (@lem5354566)). Qed.
Lemma lem5354569 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5354570 : term309 = term254.
Proof. exact (@lem5354569 term254). Qed.
Lemma lem5354571 : term609 = term254.
Proof. exact (TRANS (@lem5354567) (@lem5354570)). Qed.
Lemma lem5354572 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5354573 : term620 = term390.
Proof. exact (MK_COMB (@lem5354572) (@lem5354571)). Qed.
Lemma lem5354574 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5354575 (_69726 : int) : (term606 _69726) = (term621 _69726).
Proof. exact (MK_COMB (@lem5354573) (@lem5354574 _69726)). Qed.
Lemma lem5354576 (_69726 : int) : (term605 _69726) = (term621 _69726).
Proof. exact (TRANS (@lem5354473 _69726) (@lem5354575 _69726)). Qed.
Lemma lem5354577 (_69726 : int) : (term621 _69726) = term254.
Proof. exact (@lem1982719 (real_of_int _69726)). Qed.
Lemma lem5354578 (_69726 : int) : (term605 _69726) = term254.
Proof. exact (TRANS (@lem5354576 _69726) (@lem5354577 _69726)). Qed.
Lemma lem5354579 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354580 (_69726 : int) : (term622 _69726) = term623.
Proof. exact (MK_COMB (@lem5354579) (@lem5354578 _69726)). Qed.
Lemma lem5354581 : term312 = term312.
Proof. exact (eq_refl term312). Qed.
Lemma lem5354582 (_69726 : int) : (term661 _69726) = term628.
Proof. exact (MK_COMB (@lem5354580 _69726) (@lem5354581)). Qed.
Lemma lem5354583 (_69726 : int) : (term660 _69726) = term628.
Proof. exact (TRANS (@lem5354472 _69726) (@lem5354582 _69726)). Qed.
Lemma lem5354584 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5354585 (_69726 : int) : (term660 _69726) = term312.
Proof. exact (TRANS (@lem5354583 _69726) (@lem5354584)). Qed.
Lemma lem5354586 (_69724 : int) (_69726 : int) : (term658 _69724 _69726) = term628.
Proof. exact (MK_COMB (@lem5354471 _69724) (@lem5354585 _69726)). Qed.
Lemma lem5354587 (_69724 : int) (_69726 : int) : (term657 _69724 _69726) = term628.
Proof. exact (TRANS (@lem5354363 _69724 _69726) (@lem5354586 _69724 _69726)). Qed.
Lemma lem5354588 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5354589 (_69724 : int) (_69726 : int) : (term657 _69724 _69726) = term312.
Proof. exact (TRANS (@lem5354587 _69724 _69726) (@lem5354588)). Qed.
Lemma lem5354590 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5354591 (_69724 : int) (_69726 : int) : (term662 _69724 _69726) = term630.
Proof. exact (MK_COMB (@lem5354590) (@lem5354589 _69724 _69726)). Qed.
Lemma lem5354592 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5354593 (_69724 : int) (_69726 : int) : (term656 _69724 _69726) = term631.
Proof. exact (MK_COMB (@lem5354591 _69724 _69726) (@lem5354592)). Qed.
Lemma lem5354594 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : term631.
Proof. exact (EQ_MP (@lem5354593 _69724 _69726) (@lem5354362 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354596 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5354597 : term631 = term632.
Proof. exact (@lem5354596 term254 term312). Qed.
Lemma lem5354599 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5354600 : term312 = term313.
Proof. exact (@lem5354599 term146). Qed.
Lemma lem5354602 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354603 : term254 = term309.
Proof. exact (@lem5354602 (NUMERAL 0)). Qed.
Lemma lem5354604 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5354605 : term256 = term633.
Proof. exact (MK_COMB (@lem5354604) (@lem5354603)). Qed.
Lemma lem5354606 : term632 = term634.
Proof. exact (MK_COMB (@lem5354605) (@lem5354600)). Qed.
Lemma lem5354607 : term635.
Proof. exact (@lem1980026 term254 term267 term312 term267). Qed.
Lemma lem5354609 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354610 : term380 = term381.
Proof. exact (@lem5354609 (NUMERAL 0) term146). Qed.
Lemma lem5354611 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354612 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354613 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354612 h1) (fun h1 : term381 = True => @lem5354611)). Qed.
Lemma lem5354614 : term381 = True.
Proof. exact (EQ_MP (@lem5354613) (@lem5354611)). Qed.
Lemma lem5354615 : term380 = True.
Proof. exact (TRANS (@lem5354610) (@lem5354614)). Qed.
Lemma lem5354616 : True = term380.
Proof. exact (SYM (@lem5354615)). Qed.
Lemma lem5354617 : term380.
Proof. exact (EQ_MP (@lem5354616) (@lem0)). Qed.
Lemma lem5354618 : term636.
Proof. exact (@lem5354607 (@lem5354617)). Qed.
Lemma lem5354620 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354621 : term380 = term381.
Proof. exact (@lem5354620 (NUMERAL 0) term146). Qed.
Lemma lem5354622 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354623 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354624 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354623 h1) (fun h1 : term381 = True => @lem5354622)). Qed.
Lemma lem5354625 : term381 = True.
Proof. exact (EQ_MP (@lem5354624) (@lem5354622)). Qed.
Lemma lem5354626 : term380 = True.
Proof. exact (TRANS (@lem5354621) (@lem5354625)). Qed.
Lemma lem5354627 : True = term380.
Proof. exact (SYM (@lem5354626)). Qed.
Lemma lem5354628 : term380.
Proof. exact (EQ_MP (@lem5354627) (@lem0)). Qed.
Lemma lem5354629 : term634 = term637.
Proof. exact (@lem5354618 (@lem5354628)). Qed.
Lemma lem5354631 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5354632 : term347 = term352.
Proof. exact (@lem5354631 term146 term146). Qed.
Lemma lem5354633 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354634 : term324 = term146.
Proof. exact (EQ_MP (@lem5354633) (@lem940073)). Qed.
Lemma lem5354635 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354636 : term322 = term267.
Proof. exact (MK_COMB (@lem5354635) (@lem5354634)). Qed.
Lemma lem5354637 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5354638 : term352 = term312.
Proof. exact (MK_COMB (@lem5354637) (@lem5354636)). Qed.
Lemma lem5354639 : term347 = term312.
Proof. exact (TRANS (@lem5354632) (@lem5354638)). Qed.
Lemma lem5354641 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354642 : term392 = term254.
Proof. exact (@lem5354641 term146). Qed.
Lemma lem5354643 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5354644 : term638 = term256.
Proof. exact (MK_COMB (@lem5354643) (@lem5354642)). Qed.
Lemma lem5354645 : term637 = term632.
Proof. exact (MK_COMB (@lem5354644) (@lem5354639)). Qed.
Lemma lem5354647 (m : nat) (n : nat) : (term639 m n) = (term640 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5354648 : term632 = term641.
Proof. exact (@lem5354647 (NUMERAL 0) term146). Qed.
Lemma lem5354649 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354650 (h1 : term382 = (BIT1 0)) : (term146 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5354651 : (term382 = (BIT1 0)) = ((term146 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354650 h1) (fun h1 : (term146 = (NUMERAL 0)) = False => @lem5354649)). Qed.
Lemma lem5354652 : (term146 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5354651) (@lem5354649)). Qed.
Lemma lem5354653 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5354654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5354655 : term642 = (and True).
Proof. exact (MK_COMB (@lem5354654) (@lem5354653)). Qed.
Lemma lem5354656 : term641 = (True /\ False).
Proof. exact (MK_COMB (@lem5354655) (@lem5354652)). Qed.
Lemma lem5354658 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5354659 : term641 = False.
Proof. exact (TRANS (@lem5354656) (@lem5354658)). Qed.
Lemma lem5354660 : term632 = False.
Proof. exact (TRANS (@lem5354648) (@lem5354659)). Qed.
Lemma lem5354661 : term637 = False.
Proof. exact (TRANS (@lem5354645) (@lem5354660)). Qed.
Lemma lem5354662 : term634 = False.
Proof. exact (TRANS (@lem5354629) (@lem5354661)). Qed.
Lemma lem5354663 : term632 = False.
Proof. exact (TRANS (@lem5354606) (@lem5354662)). Qed.
Lemma lem5354664 : term631 = False.
Proof. exact (TRANS (@lem5354597) (@lem5354663)). Qed.
Lemma lem5354665 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term643 _69724 _69725 _69726) : False.
Proof. exact (EQ_MP (@lem5354664) (@lem5354594 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354666 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term570 _69724 _69725 _69726) : False.
Proof. exact (or_elim (@lem5353723 _69724 _69725 _69726 h1) (fun h0 : term579 _69724 _69725 _69726 => @lem5354194 _69724 _69725 _69726 h0) (fun h0 : term643 _69724 _69725 _69726 => @lem5354665 _69724 _69725 _69726 h0)). Qed.
Lemma lem5354667 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term566 _69724 _69725 _69726) : term566 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5354668 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term663 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5354669 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term567 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5354668 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354671 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term536 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5354669 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354673 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term505 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5354671 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354675 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term474 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5354673 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354677 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term404 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5354675 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354678 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term444 _69724 _69725 _69726.
Proof. exact (proj1 (@lem5354675 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354679 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term363 _69725 _69726.
Proof. exact (proj2 (@lem5354678 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354681 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term398 _69725 _69726.
Proof. exact (proj2 (@lem5354677 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354684 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5354685 : term580 = term380.
Proof. exact (@lem5354684 term254 term267). Qed.
Lemma lem5354687 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354688 : term267 = term346.
Proof. exact (@lem5354687 term146). Qed.
Lemma lem5354690 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354691 : term254 = term309.
Proof. exact (@lem5354690 (NUMERAL 0)). Qed.
Lemma lem5354692 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5354693 : term581 = term582.
Proof. exact (MK_COMB (@lem5354692) (@lem5354691)). Qed.
Lemma lem5354694 : term380 = term583.
Proof. exact (MK_COMB (@lem5354693) (@lem5354688)). Qed.
Lemma lem5354695 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5354697 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354698 : term380 = term381.
Proof. exact (@lem5354697 (NUMERAL 0) term146). Qed.
Lemma lem5354699 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354700 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354701 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354700 h1) (fun h1 : term381 = True => @lem5354699)). Qed.
Lemma lem5354702 : term381 = True.
Proof. exact (EQ_MP (@lem5354701) (@lem5354699)). Qed.
Lemma lem5354703 : term380 = True.
Proof. exact (TRANS (@lem5354698) (@lem5354702)). Qed.
Lemma lem5354704 : True = term380.
Proof. exact (SYM (@lem5354703)). Qed.
Lemma lem5354705 : term380.
Proof. exact (EQ_MP (@lem5354704) (@lem0)). Qed.
Lemma lem5354706 : term585.
Proof. exact (@lem5354695 (@lem5354705)). Qed.
Lemma lem5354708 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354709 : term380 = term381.
Proof. exact (@lem5354708 (NUMERAL 0) term146). Qed.
Lemma lem5354710 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354711 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354712 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354711 h1) (fun h1 : term381 = True => @lem5354710)). Qed.
Lemma lem5354713 : term381 = True.
Proof. exact (EQ_MP (@lem5354712) (@lem5354710)). Qed.
Lemma lem5354714 : term380 = True.
Proof. exact (TRANS (@lem5354709) (@lem5354713)). Qed.
Lemma lem5354715 : True = term380.
Proof. exact (SYM (@lem5354714)). Qed.
Lemma lem5354716 : term380.
Proof. exact (EQ_MP (@lem5354715) (@lem0)). Qed.
Lemma lem5354717 : term583 = term586.
Proof. exact (@lem5354706 (@lem5354716)). Qed.
Lemma lem5354719 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354720 : term321 = term322.
Proof. exact (@lem5354719 term146 term146). Qed.
Lemma lem5354721 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354722 : term324 = term146.
Proof. exact (EQ_MP (@lem5354721) (@lem940073)). Qed.
Lemma lem5354723 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354724 : term322 = term267.
Proof. exact (MK_COMB (@lem5354723) (@lem5354722)). Qed.
Lemma lem5354725 : term321 = term267.
Proof. exact (TRANS (@lem5354720) (@lem5354724)). Qed.
Lemma lem5354727 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354728 : term392 = term254.
Proof. exact (@lem5354727 term146). Qed.
Lemma lem5354729 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5354730 : term587 = term581.
Proof. exact (MK_COMB (@lem5354729) (@lem5354728)). Qed.
Lemma lem5354731 : term586 = term380.
Proof. exact (MK_COMB (@lem5354730) (@lem5354725)). Qed.
Lemma lem5354733 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354734 : term380 = term381.
Proof. exact (@lem5354733 (NUMERAL 0) term146). Qed.
Lemma lem5354735 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354736 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354737 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354736 h1) (fun h1 : term381 = True => @lem5354735)). Qed.
Lemma lem5354738 : term381 = True.
Proof. exact (EQ_MP (@lem5354737) (@lem5354735)). Qed.
Lemma lem5354739 : term380 = True.
Proof. exact (TRANS (@lem5354734) (@lem5354738)). Qed.
Lemma lem5354740 : term586 = True.
Proof. exact (TRANS (@lem5354731) (@lem5354739)). Qed.
Lemma lem5354741 : term583 = True.
Proof. exact (TRANS (@lem5354717) (@lem5354740)). Qed.
Lemma lem5354742 : term380 = True.
Proof. exact (TRANS (@lem5354694) (@lem5354741)). Qed.
Lemma lem5354743 : term580 = True.
Proof. exact (TRANS (@lem5354685) (@lem5354742)). Qed.
Lemma lem5354744 : True = term580.
Proof. exact (SYM (@lem5354743)). Qed.
Lemma lem5354745 : term580.
Proof. exact (EQ_MP (@lem5354744) (@lem0)). Qed.
Lemma lem5354746 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term649 _69725 _69726.
Proof. exact (conj (@lem5354745) (@lem5354681 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354748 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5354749 (_69725 : int) (_69726 : int) : term650 _69725 _69726.
Proof. exact (@lem5354748 term267 (term335 _69725 _69726)). Qed.
Lemma lem5354750 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term651 _69725 _69726.
Proof. exact (@lem5354749 _69725 _69726 (@lem5354746 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354751 (_69725 : int) (_69726 : int) : (term652 _69725 _69726) = (term335 _69725 _69726).
Proof. exact (@lem1982733 (term335 _69725 _69726)). Qed.
Lemma lem5354752 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5354753 (_69725 : int) (_69726 : int) : (term653 _69725 _69726) = (term397 _69725 _69726).
Proof. exact (MK_COMB (@lem5354752) (@lem5354751 _69725 _69726)). Qed.
Lemma lem5354754 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5354755 (_69725 : int) (_69726 : int) : (term651 _69725 _69726) = (term398 _69725 _69726).
Proof. exact (MK_COMB (@lem5354753 _69725 _69726) (@lem5354754)). Qed.
Lemma lem5354756 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term398 _69725 _69726.
Proof. exact (EQ_MP (@lem5354755 _69725 _69726) (@lem5354750 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354758 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5354759 : term580 = term380.
Proof. exact (@lem5354758 term254 term267). Qed.
Lemma lem5354761 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354762 : term267 = term346.
Proof. exact (@lem5354761 term146). Qed.
Lemma lem5354764 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354765 : term254 = term309.
Proof. exact (@lem5354764 (NUMERAL 0)). Qed.
Lemma lem5354766 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5354767 : term581 = term582.
Proof. exact (MK_COMB (@lem5354766) (@lem5354765)). Qed.
Lemma lem5354768 : term380 = term583.
Proof. exact (MK_COMB (@lem5354767) (@lem5354762)). Qed.
Lemma lem5354769 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5354771 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354772 : term380 = term381.
Proof. exact (@lem5354771 (NUMERAL 0) term146). Qed.
Lemma lem5354773 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354774 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354775 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354774 h1) (fun h1 : term381 = True => @lem5354773)). Qed.
Lemma lem5354776 : term381 = True.
Proof. exact (EQ_MP (@lem5354775) (@lem5354773)). Qed.
Lemma lem5354777 : term380 = True.
Proof. exact (TRANS (@lem5354772) (@lem5354776)). Qed.
Lemma lem5354778 : True = term380.
Proof. exact (SYM (@lem5354777)). Qed.
Lemma lem5354779 : term380.
Proof. exact (EQ_MP (@lem5354778) (@lem0)). Qed.
Lemma lem5354780 : term585.
Proof. exact (@lem5354769 (@lem5354779)). Qed.
Lemma lem5354782 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354783 : term380 = term381.
Proof. exact (@lem5354782 (NUMERAL 0) term146). Qed.
Lemma lem5354784 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354785 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354786 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354785 h1) (fun h1 : term381 = True => @lem5354784)). Qed.
Lemma lem5354787 : term381 = True.
Proof. exact (EQ_MP (@lem5354786) (@lem5354784)). Qed.
Lemma lem5354788 : term380 = True.
Proof. exact (TRANS (@lem5354783) (@lem5354787)). Qed.
Lemma lem5354789 : True = term380.
Proof. exact (SYM (@lem5354788)). Qed.
Lemma lem5354790 : term380.
Proof. exact (EQ_MP (@lem5354789) (@lem0)). Qed.
Lemma lem5354791 : term583 = term586.
Proof. exact (@lem5354780 (@lem5354790)). Qed.
Lemma lem5354793 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354794 : term321 = term322.
Proof. exact (@lem5354793 term146 term146). Qed.
Lemma lem5354795 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354796 : term324 = term146.
Proof. exact (EQ_MP (@lem5354795) (@lem940073)). Qed.
Lemma lem5354797 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354798 : term322 = term267.
Proof. exact (MK_COMB (@lem5354797) (@lem5354796)). Qed.
Lemma lem5354799 : term321 = term267.
Proof. exact (TRANS (@lem5354794) (@lem5354798)). Qed.
Lemma lem5354801 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354802 : term392 = term254.
Proof. exact (@lem5354801 term146). Qed.
Lemma lem5354803 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5354804 : term587 = term581.
Proof. exact (MK_COMB (@lem5354803) (@lem5354802)). Qed.
Lemma lem5354805 : term586 = term380.
Proof. exact (MK_COMB (@lem5354804) (@lem5354799)). Qed.
Lemma lem5354807 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354808 : term380 = term381.
Proof. exact (@lem5354807 (NUMERAL 0) term146). Qed.
Lemma lem5354809 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354810 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354811 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354810 h1) (fun h1 : term381 = True => @lem5354809)). Qed.
Lemma lem5354812 : term381 = True.
Proof. exact (EQ_MP (@lem5354811) (@lem5354809)). Qed.
Lemma lem5354813 : term380 = True.
Proof. exact (TRANS (@lem5354808) (@lem5354812)). Qed.
Lemma lem5354814 : term586 = True.
Proof. exact (TRANS (@lem5354805) (@lem5354813)). Qed.
Lemma lem5354815 : term583 = True.
Proof. exact (TRANS (@lem5354791) (@lem5354814)). Qed.
Lemma lem5354816 : term380 = True.
Proof. exact (TRANS (@lem5354768) (@lem5354815)). Qed.
Lemma lem5354817 : term580 = True.
Proof. exact (TRANS (@lem5354759) (@lem5354816)). Qed.
Lemma lem5354818 : True = term580.
Proof. exact (SYM (@lem5354817)). Qed.
Lemma lem5354819 : term580.
Proof. exact (EQ_MP (@lem5354818) (@lem0)). Qed.
Lemma lem5354820 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term644 _69725 _69726.
Proof. exact (conj (@lem5354819) (@lem5354679 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354822 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5354823 (_69725 : int) (_69726 : int) : term645 _69725 _69726.
Proof. exact (@lem5354822 term267 (term361 _69725 _69726)). Qed.
Lemma lem5354824 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term646 _69725 _69726.
Proof. exact (@lem5354823 _69725 _69726 (@lem5354820 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354825 (_69725 : int) (_69726 : int) : (term647 _69725 _69726) = (term361 _69725 _69726).
Proof. exact (@lem1982733 (term361 _69725 _69726)). Qed.
Lemma lem5354826 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5354827 (_69725 : int) (_69726 : int) : (term648 _69725 _69726) = (term362 _69725 _69726).
Proof. exact (MK_COMB (@lem5354826) (@lem5354825 _69725 _69726)). Qed.
Lemma lem5354828 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5354829 (_69725 : int) (_69726 : int) : (term646 _69725 _69726) = (term363 _69725 _69726).
Proof. exact (MK_COMB (@lem5354827 _69725 _69726) (@lem5354828)). Qed.
Lemma lem5354830 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term363 _69725 _69726.
Proof. exact (EQ_MP (@lem5354829 _69725 _69726) (@lem5354824 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354831 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term449 _69725 _69726.
Proof. exact (conj (@lem5354830 _69724 _69725 _69726 h1) (@lem5354756 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354833 (x : real) (y : real) : term600 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5354834 (_69725 : int) (_69726 : int) : term664 _69725 _69726.
Proof. exact (@lem5354833 (term361 _69725 _69726) (term335 _69725 _69726)). Qed.
Lemma lem5354835 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term665 _69725 _69726.
Proof. exact (@lem5354834 _69725 _69726 (@lem5354831 _69724 _69725 _69726 h1)). Qed.
Lemma lem5354836 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = (term667 _69725 _69726).
Proof. exact (@lem1982753 (term337 _69725) (real_of_int _69725) (term659 _69726) (term337 _69726)). Qed.
Lemma lem5354837 (_69725 : int) : (term605 _69725) = (term606 _69725).
Proof. exact (@lem1982713 term312 (real_of_int _69725)). Qed.
Lemma lem5354839 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354840 : term267 = term346.
Proof. exact (@lem5354839 term146). Qed.
Lemma lem5354842 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5354843 : term312 = term313.
Proof. exact (@lem5354842 term146). Qed.
Lemma lem5354844 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354845 : term607 = term608.
Proof. exact (MK_COMB (@lem5354844) (@lem5354843)). Qed.
Lemma lem5354846 : term609 = term610.
Proof. exact (MK_COMB (@lem5354845) (@lem5354840)). Qed.
Lemma lem5354847 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5354849 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354850 : term380 = term381.
Proof. exact (@lem5354849 (NUMERAL 0) term146). Qed.
Lemma lem5354851 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354852 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354853 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354852 h1) (fun h1 : term381 = True => @lem5354851)). Qed.
Lemma lem5354854 : term381 = True.
Proof. exact (EQ_MP (@lem5354853) (@lem5354851)). Qed.
Lemma lem5354855 : term380 = True.
Proof. exact (TRANS (@lem5354850) (@lem5354854)). Qed.
Lemma lem5354856 : True = term380.
Proof. exact (SYM (@lem5354855)). Qed.
Lemma lem5354857 : term380.
Proof. exact (EQ_MP (@lem5354856) (@lem0)). Qed.
Lemma lem5354858 : term612.
Proof. exact (@lem5354847 (@lem5354857)). Qed.
Lemma lem5354860 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354861 : term380 = term381.
Proof. exact (@lem5354860 (NUMERAL 0) term146). Qed.
Lemma lem5354862 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354863 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354864 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354863 h1) (fun h1 : term381 = True => @lem5354862)). Qed.
Lemma lem5354865 : term381 = True.
Proof. exact (EQ_MP (@lem5354864) (@lem5354862)). Qed.
Lemma lem5354866 : term380 = True.
Proof. exact (TRANS (@lem5354861) (@lem5354865)). Qed.
Lemma lem5354867 : True = term380.
Proof. exact (SYM (@lem5354866)). Qed.
Lemma lem5354868 : term380.
Proof. exact (EQ_MP (@lem5354867) (@lem0)). Qed.
Lemma lem5354869 : term613.
Proof. exact (@lem5354858 (@lem5354868)). Qed.
Lemma lem5354871 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354872 : term380 = term381.
Proof. exact (@lem5354871 (NUMERAL 0) term146). Qed.
Lemma lem5354873 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354874 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354875 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354874 h1) (fun h1 : term381 = True => @lem5354873)). Qed.
Lemma lem5354876 : term381 = True.
Proof. exact (EQ_MP (@lem5354875) (@lem5354873)). Qed.
Lemma lem5354877 : term380 = True.
Proof. exact (TRANS (@lem5354872) (@lem5354876)). Qed.
Lemma lem5354878 : True = term380.
Proof. exact (SYM (@lem5354877)). Qed.
Lemma lem5354879 : term380.
Proof. exact (EQ_MP (@lem5354878) (@lem0)). Qed.
Lemma lem5354880 : term614.
Proof. exact (@lem5354869 (@lem5354879)). Qed.
Lemma lem5354882 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354883 : term321 = term322.
Proof. exact (@lem5354882 term146 term146). Qed.
Lemma lem5354884 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354885 : term324 = term146.
Proof. exact (EQ_MP (@lem5354884) (@lem940073)). Qed.
Lemma lem5354886 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354887 : term322 = term267.
Proof. exact (MK_COMB (@lem5354886) (@lem5354885)). Qed.
Lemma lem5354888 : term321 = term267.
Proof. exact (TRANS (@lem5354883) (@lem5354887)). Qed.
Lemma lem5354890 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5354891 : term347 = term352.
Proof. exact (@lem5354890 term146 term146). Qed.
Lemma lem5354892 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354893 : term324 = term146.
Proof. exact (EQ_MP (@lem5354892) (@lem940073)). Qed.
Lemma lem5354894 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354895 : term322 = term267.
Proof. exact (MK_COMB (@lem5354894) (@lem5354893)). Qed.
Lemma lem5354896 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5354897 : term352 = term312.
Proof. exact (MK_COMB (@lem5354896) (@lem5354895)). Qed.
Lemma lem5354898 : term347 = term312.
Proof. exact (TRANS (@lem5354891) (@lem5354897)). Qed.
Lemma lem5354899 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354900 : term615 = term607.
Proof. exact (MK_COMB (@lem5354899) (@lem5354898)). Qed.
Lemma lem5354901 : term616 = term609.
Proof. exact (MK_COMB (@lem5354900) (@lem5354888)). Qed.
Lemma lem5354903 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5354904 : term609 = term254.
Proof. exact (@lem5354903 term146). Qed.
Lemma lem5354905 : term616 = term254.
Proof. exact (TRANS (@lem5354901) (@lem5354904)). Qed.
Lemma lem5354906 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5354907 : term618 = term390.
Proof. exact (MK_COMB (@lem5354906) (@lem5354905)). Qed.
Lemma lem5354908 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5354909 : term619 = term392.
Proof. exact (MK_COMB (@lem5354907) (@lem5354908)). Qed.
Lemma lem5354911 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354912 : term392 = term254.
Proof. exact (@lem5354911 term146). Qed.
Lemma lem5354913 : term619 = term254.
Proof. exact (TRANS (@lem5354909) (@lem5354912)). Qed.
Lemma lem5354915 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354916 : term321 = term322.
Proof. exact (@lem5354915 term146 term146). Qed.
Lemma lem5354917 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354918 : term324 = term146.
Proof. exact (EQ_MP (@lem5354917) (@lem940073)). Qed.
Lemma lem5354919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354920 : term322 = term267.
Proof. exact (MK_COMB (@lem5354919) (@lem5354918)). Qed.
Lemma lem5354921 : term321 = term267.
Proof. exact (TRANS (@lem5354916) (@lem5354920)). Qed.
Lemma lem5354922 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5354923 : term394 = term392.
Proof. exact (MK_COMB (@lem5354922) (@lem5354921)). Qed.
Lemma lem5354925 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5354926 : term392 = term254.
Proof. exact (@lem5354925 term146). Qed.
Lemma lem5354927 : term394 = term254.
Proof. exact (TRANS (@lem5354923) (@lem5354926)). Qed.
Lemma lem5354928 : term254 = term394.
Proof. exact (SYM (@lem5354927)). Qed.
Lemma lem5354929 : term619 = term394.
Proof. exact (TRANS (@lem5354913) (@lem5354928)). Qed.
Lemma lem5354930 : term610 = term309.
Proof. exact (@lem5354880 (@lem5354929)). Qed.
Lemma lem5354931 : term609 = term309.
Proof. exact (TRANS (@lem5354846) (@lem5354930)). Qed.
Lemma lem5354933 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5354934 : term309 = term254.
Proof. exact (@lem5354933 term254). Qed.
Lemma lem5354935 : term609 = term254.
Proof. exact (TRANS (@lem5354931) (@lem5354934)). Qed.
Lemma lem5354936 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5354937 : term620 = term390.
Proof. exact (MK_COMB (@lem5354936) (@lem5354935)). Qed.
Lemma lem5354938 (_69725 : int) : (real_of_int _69725) = (real_of_int _69725).
Proof. exact (eq_refl (real_of_int _69725)). Qed.
Lemma lem5354939 (_69725 : int) : (term606 _69725) = (term621 _69725).
Proof. exact (MK_COMB (@lem5354937) (@lem5354938 _69725)). Qed.
Lemma lem5354940 (_69725 : int) : (term605 _69725) = (term621 _69725).
Proof. exact (TRANS (@lem5354837 _69725) (@lem5354939 _69725)). Qed.
Lemma lem5354941 (_69725 : int) : (term621 _69725) = term254.
Proof. exact (@lem1982719 (real_of_int _69725)). Qed.
Lemma lem5354942 (_69725 : int) : (term605 _69725) = term254.
Proof. exact (TRANS (@lem5354940 _69725) (@lem5354941 _69725)). Qed.
Lemma lem5354943 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354944 (_69725 : int) : (term622 _69725) = term623.
Proof. exact (MK_COMB (@lem5354943) (@lem5354942 _69725)). Qed.
Lemma lem5354945 (_69726 : int) : (term668 _69726) = (term625 _69726).
Proof. exact (@lem1982759 (real_of_int _69726) (term337 _69726) term312). Qed.
Lemma lem5354946 (_69726 : int) : (term626 _69726) = (term606 _69726).
Proof. exact (@lem1982715 term312 (real_of_int _69726)). Qed.
Lemma lem5354948 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5354949 : term267 = term346.
Proof. exact (@lem5354948 term146). Qed.
Lemma lem5354951 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5354952 : term312 = term313.
Proof. exact (@lem5354951 term146). Qed.
Lemma lem5354953 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5354954 : term607 = term608.
Proof. exact (MK_COMB (@lem5354953) (@lem5354952)). Qed.
Lemma lem5354955 : term609 = term610.
Proof. exact (MK_COMB (@lem5354954) (@lem5354949)). Qed.
Lemma lem5354956 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5354958 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354959 : term380 = term381.
Proof. exact (@lem5354958 (NUMERAL 0) term146). Qed.
Lemma lem5354960 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354961 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354962 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354961 h1) (fun h1 : term381 = True => @lem5354960)). Qed.
Lemma lem5354963 : term381 = True.
Proof. exact (EQ_MP (@lem5354962) (@lem5354960)). Qed.
Lemma lem5354964 : term380 = True.
Proof. exact (TRANS (@lem5354959) (@lem5354963)). Qed.
Lemma lem5354965 : True = term380.
Proof. exact (SYM (@lem5354964)). Qed.
Lemma lem5354966 : term380.
Proof. exact (EQ_MP (@lem5354965) (@lem0)). Qed.
Lemma lem5354967 : term612.
Proof. exact (@lem5354956 (@lem5354966)). Qed.
Lemma lem5354969 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354970 : term380 = term381.
Proof. exact (@lem5354969 (NUMERAL 0) term146). Qed.
Lemma lem5354971 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354972 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354973 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354972 h1) (fun h1 : term381 = True => @lem5354971)). Qed.
Lemma lem5354974 : term381 = True.
Proof. exact (EQ_MP (@lem5354973) (@lem5354971)). Qed.
Lemma lem5354975 : term380 = True.
Proof. exact (TRANS (@lem5354970) (@lem5354974)). Qed.
Lemma lem5354976 : True = term380.
Proof. exact (SYM (@lem5354975)). Qed.
Lemma lem5354977 : term380.
Proof. exact (EQ_MP (@lem5354976) (@lem0)). Qed.
Lemma lem5354978 : term613.
Proof. exact (@lem5354967 (@lem5354977)). Qed.
Lemma lem5354980 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5354981 : term380 = term381.
Proof. exact (@lem5354980 (NUMERAL 0) term146). Qed.
Lemma lem5354982 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5354983 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5354984 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5354983 h1) (fun h1 : term381 = True => @lem5354982)). Qed.
Lemma lem5354985 : term381 = True.
Proof. exact (EQ_MP (@lem5354984) (@lem5354982)). Qed.
Lemma lem5354986 : term380 = True.
Proof. exact (TRANS (@lem5354981) (@lem5354985)). Qed.
Lemma lem5354987 : True = term380.
Proof. exact (SYM (@lem5354986)). Qed.
Lemma lem5354988 : term380.
Proof. exact (EQ_MP (@lem5354987) (@lem0)). Qed.
Lemma lem5354989 : term614.
Proof. exact (@lem5354978 (@lem5354988)). Qed.
Lemma lem5354991 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5354992 : term321 = term322.
Proof. exact (@lem5354991 term146 term146). Qed.
Lemma lem5354993 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5354994 : term324 = term146.
Proof. exact (EQ_MP (@lem5354993) (@lem940073)). Qed.
Lemma lem5354995 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5354996 : term322 = term267.
Proof. exact (MK_COMB (@lem5354995) (@lem5354994)). Qed.
Lemma lem5354997 : term321 = term267.
Proof. exact (TRANS (@lem5354992) (@lem5354996)). Qed.
Lemma lem5354999 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5355000 : term347 = term352.
Proof. exact (@lem5354999 term146 term146). Qed.
Lemma lem5355001 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355002 : term324 = term146.
Proof. exact (EQ_MP (@lem5355001) (@lem940073)). Qed.
Lemma lem5355003 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355004 : term322 = term267.
Proof. exact (MK_COMB (@lem5355003) (@lem5355002)). Qed.
Lemma lem5355005 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5355006 : term352 = term312.
Proof. exact (MK_COMB (@lem5355005) (@lem5355004)). Qed.
Lemma lem5355007 : term347 = term312.
Proof. exact (TRANS (@lem5355000) (@lem5355006)). Qed.
Lemma lem5355008 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355009 : term615 = term607.
Proof. exact (MK_COMB (@lem5355008) (@lem5355007)). Qed.
Lemma lem5355010 : term616 = term609.
Proof. exact (MK_COMB (@lem5355009) (@lem5354997)). Qed.
Lemma lem5355012 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5355013 : term609 = term254.
Proof. exact (@lem5355012 term146). Qed.
Lemma lem5355014 : term616 = term254.
Proof. exact (TRANS (@lem5355010) (@lem5355013)). Qed.
Lemma lem5355015 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5355016 : term618 = term390.
Proof. exact (MK_COMB (@lem5355015) (@lem5355014)). Qed.
Lemma lem5355017 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5355018 : term619 = term392.
Proof. exact (MK_COMB (@lem5355016) (@lem5355017)). Qed.
Lemma lem5355020 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355021 : term392 = term254.
Proof. exact (@lem5355020 term146). Qed.
Lemma lem5355022 : term619 = term254.
Proof. exact (TRANS (@lem5355018) (@lem5355021)). Qed.
Lemma lem5355024 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355025 : term321 = term322.
Proof. exact (@lem5355024 term146 term146). Qed.
Lemma lem5355026 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355027 : term324 = term146.
Proof. exact (EQ_MP (@lem5355026) (@lem940073)). Qed.
Lemma lem5355028 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355029 : term322 = term267.
Proof. exact (MK_COMB (@lem5355028) (@lem5355027)). Qed.
Lemma lem5355030 : term321 = term267.
Proof. exact (TRANS (@lem5355025) (@lem5355029)). Qed.
Lemma lem5355031 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5355032 : term394 = term392.
Proof. exact (MK_COMB (@lem5355031) (@lem5355030)). Qed.
Lemma lem5355034 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355035 : term392 = term254.
Proof. exact (@lem5355034 term146). Qed.
Lemma lem5355036 : term394 = term254.
Proof. exact (TRANS (@lem5355032) (@lem5355035)). Qed.
Lemma lem5355037 : term254 = term394.
Proof. exact (SYM (@lem5355036)). Qed.
Lemma lem5355038 : term619 = term394.
Proof. exact (TRANS (@lem5355022) (@lem5355037)). Qed.
Lemma lem5355039 : term610 = term309.
Proof. exact (@lem5354989 (@lem5355038)). Qed.
Lemma lem5355040 : term609 = term309.
Proof. exact (TRANS (@lem5354955) (@lem5355039)). Qed.
Lemma lem5355042 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5355043 : term309 = term254.
Proof. exact (@lem5355042 term254). Qed.
Lemma lem5355044 : term609 = term254.
Proof. exact (TRANS (@lem5355040) (@lem5355043)). Qed.
Lemma lem5355045 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5355046 : term620 = term390.
Proof. exact (MK_COMB (@lem5355045) (@lem5355044)). Qed.
Lemma lem5355047 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5355048 (_69726 : int) : (term606 _69726) = (term621 _69726).
Proof. exact (MK_COMB (@lem5355046) (@lem5355047 _69726)). Qed.
Lemma lem5355049 (_69726 : int) : (term626 _69726) = (term621 _69726).
Proof. exact (TRANS (@lem5354946 _69726) (@lem5355048 _69726)). Qed.
Lemma lem5355050 (_69726 : int) : (term621 _69726) = term254.
Proof. exact (@lem1982719 (real_of_int _69726)). Qed.
Lemma lem5355051 (_69726 : int) : (term626 _69726) = term254.
Proof. exact (TRANS (@lem5355049 _69726) (@lem5355050 _69726)). Qed.
Lemma lem5355052 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355053 (_69726 : int) : (term627 _69726) = term623.
Proof. exact (MK_COMB (@lem5355052) (@lem5355051 _69726)). Qed.
Lemma lem5355054 : term312 = term312.
Proof. exact (eq_refl term312). Qed.
Lemma lem5355055 (_69726 : int) : (term625 _69726) = term628.
Proof. exact (MK_COMB (@lem5355053 _69726) (@lem5355054)). Qed.
Lemma lem5355056 (_69726 : int) : (term668 _69726) = term628.
Proof. exact (TRANS (@lem5354945 _69726) (@lem5355055 _69726)). Qed.
Lemma lem5355057 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5355058 (_69726 : int) : (term668 _69726) = term312.
Proof. exact (TRANS (@lem5355056 _69726) (@lem5355057)). Qed.
Lemma lem5355059 (_69725 : int) (_69726 : int) : (term667 _69725 _69726) = term628.
Proof. exact (MK_COMB (@lem5354944 _69725) (@lem5355058 _69726)). Qed.
Lemma lem5355060 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = term628.
Proof. exact (TRANS (@lem5354836 _69725 _69726) (@lem5355059 _69725 _69726)). Qed.
Lemma lem5355061 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5355062 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = term312.
Proof. exact (TRANS (@lem5355060 _69725 _69726) (@lem5355061)). Qed.
Lemma lem5355063 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5355064 (_69725 : int) (_69726 : int) : (term669 _69725 _69726) = term630.
Proof. exact (MK_COMB (@lem5355063) (@lem5355062 _69725 _69726)). Qed.
Lemma lem5355065 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5355066 (_69725 : int) (_69726 : int) : (term665 _69725 _69726) = term631.
Proof. exact (MK_COMB (@lem5355064 _69725 _69726) (@lem5355065)). Qed.
Lemma lem5355067 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : term631.
Proof. exact (EQ_MP (@lem5355066 _69725 _69726) (@lem5354835 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355069 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5355070 : term631 = term632.
Proof. exact (@lem5355069 term254 term312). Qed.
Lemma lem5355072 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5355073 : term312 = term313.
Proof. exact (@lem5355072 term146). Qed.
Lemma lem5355075 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355076 : term254 = term309.
Proof. exact (@lem5355075 (NUMERAL 0)). Qed.
Lemma lem5355077 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5355078 : term256 = term633.
Proof. exact (MK_COMB (@lem5355077) (@lem5355076)). Qed.
Lemma lem5355079 : term632 = term634.
Proof. exact (MK_COMB (@lem5355078) (@lem5355073)). Qed.
Lemma lem5355080 : term635.
Proof. exact (@lem1980026 term254 term267 term312 term267). Qed.
Lemma lem5355082 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355083 : term380 = term381.
Proof. exact (@lem5355082 (NUMERAL 0) term146). Qed.
Lemma lem5355084 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355085 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355086 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355085 h1) (fun h1 : term381 = True => @lem5355084)). Qed.
Lemma lem5355087 : term381 = True.
Proof. exact (EQ_MP (@lem5355086) (@lem5355084)). Qed.
Lemma lem5355088 : term380 = True.
Proof. exact (TRANS (@lem5355083) (@lem5355087)). Qed.
Lemma lem5355089 : True = term380.
Proof. exact (SYM (@lem5355088)). Qed.
Lemma lem5355090 : term380.
Proof. exact (EQ_MP (@lem5355089) (@lem0)). Qed.
Lemma lem5355091 : term636.
Proof. exact (@lem5355080 (@lem5355090)). Qed.
Lemma lem5355093 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355094 : term380 = term381.
Proof. exact (@lem5355093 (NUMERAL 0) term146). Qed.
Lemma lem5355095 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355096 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355097 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355096 h1) (fun h1 : term381 = True => @lem5355095)). Qed.
Lemma lem5355098 : term381 = True.
Proof. exact (EQ_MP (@lem5355097) (@lem5355095)). Qed.
Lemma lem5355099 : term380 = True.
Proof. exact (TRANS (@lem5355094) (@lem5355098)). Qed.
Lemma lem5355100 : True = term380.
Proof. exact (SYM (@lem5355099)). Qed.
Lemma lem5355101 : term380.
Proof. exact (EQ_MP (@lem5355100) (@lem0)). Qed.
Lemma lem5355102 : term634 = term637.
Proof. exact (@lem5355091 (@lem5355101)). Qed.
Lemma lem5355104 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5355105 : term347 = term352.
Proof. exact (@lem5355104 term146 term146). Qed.
Lemma lem5355106 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355107 : term324 = term146.
Proof. exact (EQ_MP (@lem5355106) (@lem940073)). Qed.
Lemma lem5355108 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355109 : term322 = term267.
Proof. exact (MK_COMB (@lem5355108) (@lem5355107)). Qed.
Lemma lem5355110 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5355111 : term352 = term312.
Proof. exact (MK_COMB (@lem5355110) (@lem5355109)). Qed.
Lemma lem5355112 : term347 = term312.
Proof. exact (TRANS (@lem5355105) (@lem5355111)). Qed.
Lemma lem5355114 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355115 : term392 = term254.
Proof. exact (@lem5355114 term146). Qed.
Lemma lem5355116 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5355117 : term638 = term256.
Proof. exact (MK_COMB (@lem5355116) (@lem5355115)). Qed.
Lemma lem5355118 : term637 = term632.
Proof. exact (MK_COMB (@lem5355117) (@lem5355112)). Qed.
Lemma lem5355120 (m : nat) (n : nat) : (term639 m n) = (term640 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5355121 : term632 = term641.
Proof. exact (@lem5355120 (NUMERAL 0) term146). Qed.
Lemma lem5355122 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355123 (h1 : term382 = (BIT1 0)) : (term146 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5355124 : (term382 = (BIT1 0)) = ((term146 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355123 h1) (fun h1 : (term146 = (NUMERAL 0)) = False => @lem5355122)). Qed.
Lemma lem5355125 : (term146 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5355124) (@lem5355122)). Qed.
Lemma lem5355126 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5355127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5355128 : term642 = (and True).
Proof. exact (MK_COMB (@lem5355127) (@lem5355126)). Qed.
Lemma lem5355129 : term641 = (True /\ False).
Proof. exact (MK_COMB (@lem5355128) (@lem5355125)). Qed.
Lemma lem5355131 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5355132 : term641 = False.
Proof. exact (TRANS (@lem5355129) (@lem5355131)). Qed.
Lemma lem5355133 : term632 = False.
Proof. exact (TRANS (@lem5355121) (@lem5355132)). Qed.
Lemma lem5355134 : term637 = False.
Proof. exact (TRANS (@lem5355118) (@lem5355133)). Qed.
Lemma lem5355135 : term634 = False.
Proof. exact (TRANS (@lem5355102) (@lem5355134)). Qed.
Lemma lem5355136 : term632 = False.
Proof. exact (TRANS (@lem5355079) (@lem5355135)). Qed.
Lemma lem5355137 : term631 = False.
Proof. exact (TRANS (@lem5355070) (@lem5355136)). Qed.
Lemma lem5355138 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term663 _69724 _69725 _69726) : False.
Proof. exact (EQ_MP (@lem5355137) (@lem5355067 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355139 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term670 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5355140 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term568 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5355139 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355142 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term537 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5355140 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355144 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term506 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5355142 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355146 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term475 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5355144 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355148 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term404 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5355146 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355149 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term445 _69724 _69725 _69726.
Proof. exact (proj1 (@lem5355146 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355150 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term363 _69725 _69726.
Proof. exact (proj2 (@lem5355149 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355152 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term398 _69725 _69726.
Proof. exact (proj2 (@lem5355148 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355155 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5355156 : term580 = term380.
Proof. exact (@lem5355155 term254 term267). Qed.
Lemma lem5355158 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355159 : term267 = term346.
Proof. exact (@lem5355158 term146). Qed.
Lemma lem5355161 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355162 : term254 = term309.
Proof. exact (@lem5355161 (NUMERAL 0)). Qed.
Lemma lem5355163 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5355164 : term581 = term582.
Proof. exact (MK_COMB (@lem5355163) (@lem5355162)). Qed.
Lemma lem5355165 : term380 = term583.
Proof. exact (MK_COMB (@lem5355164) (@lem5355159)). Qed.
Lemma lem5355166 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5355168 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355169 : term380 = term381.
Proof. exact (@lem5355168 (NUMERAL 0) term146). Qed.
Lemma lem5355170 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355171 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355172 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355171 h1) (fun h1 : term381 = True => @lem5355170)). Qed.
Lemma lem5355173 : term381 = True.
Proof. exact (EQ_MP (@lem5355172) (@lem5355170)). Qed.
Lemma lem5355174 : term380 = True.
Proof. exact (TRANS (@lem5355169) (@lem5355173)). Qed.
Lemma lem5355175 : True = term380.
Proof. exact (SYM (@lem5355174)). Qed.
Lemma lem5355176 : term380.
Proof. exact (EQ_MP (@lem5355175) (@lem0)). Qed.
Lemma lem5355177 : term585.
Proof. exact (@lem5355166 (@lem5355176)). Qed.
Lemma lem5355179 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355180 : term380 = term381.
Proof. exact (@lem5355179 (NUMERAL 0) term146). Qed.
Lemma lem5355181 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355182 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355183 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355182 h1) (fun h1 : term381 = True => @lem5355181)). Qed.
Lemma lem5355184 : term381 = True.
Proof. exact (EQ_MP (@lem5355183) (@lem5355181)). Qed.
Lemma lem5355185 : term380 = True.
Proof. exact (TRANS (@lem5355180) (@lem5355184)). Qed.
Lemma lem5355186 : True = term380.
Proof. exact (SYM (@lem5355185)). Qed.
Lemma lem5355187 : term380.
Proof. exact (EQ_MP (@lem5355186) (@lem0)). Qed.
Lemma lem5355188 : term583 = term586.
Proof. exact (@lem5355177 (@lem5355187)). Qed.
Lemma lem5355190 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355191 : term321 = term322.
Proof. exact (@lem5355190 term146 term146). Qed.
Lemma lem5355192 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355193 : term324 = term146.
Proof. exact (EQ_MP (@lem5355192) (@lem940073)). Qed.
Lemma lem5355194 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355195 : term322 = term267.
Proof. exact (MK_COMB (@lem5355194) (@lem5355193)). Qed.
Lemma lem5355196 : term321 = term267.
Proof. exact (TRANS (@lem5355191) (@lem5355195)). Qed.
Lemma lem5355198 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355199 : term392 = term254.
Proof. exact (@lem5355198 term146). Qed.
Lemma lem5355200 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5355201 : term587 = term581.
Proof. exact (MK_COMB (@lem5355200) (@lem5355199)). Qed.
Lemma lem5355202 : term586 = term380.
Proof. exact (MK_COMB (@lem5355201) (@lem5355196)). Qed.
Lemma lem5355204 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355205 : term380 = term381.
Proof. exact (@lem5355204 (NUMERAL 0) term146). Qed.
Lemma lem5355206 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355207 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355208 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355207 h1) (fun h1 : term381 = True => @lem5355206)). Qed.
Lemma lem5355209 : term381 = True.
Proof. exact (EQ_MP (@lem5355208) (@lem5355206)). Qed.
Lemma lem5355210 : term380 = True.
Proof. exact (TRANS (@lem5355205) (@lem5355209)). Qed.
Lemma lem5355211 : term586 = True.
Proof. exact (TRANS (@lem5355202) (@lem5355210)). Qed.
Lemma lem5355212 : term583 = True.
Proof. exact (TRANS (@lem5355188) (@lem5355211)). Qed.
Lemma lem5355213 : term380 = True.
Proof. exact (TRANS (@lem5355165) (@lem5355212)). Qed.
Lemma lem5355214 : term580 = True.
Proof. exact (TRANS (@lem5355156) (@lem5355213)). Qed.
Lemma lem5355215 : True = term580.
Proof. exact (SYM (@lem5355214)). Qed.
Lemma lem5355216 : term580.
Proof. exact (EQ_MP (@lem5355215) (@lem0)). Qed.
Lemma lem5355217 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term649 _69725 _69726.
Proof. exact (conj (@lem5355216) (@lem5355152 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355219 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5355220 (_69725 : int) (_69726 : int) : term650 _69725 _69726.
Proof. exact (@lem5355219 term267 (term335 _69725 _69726)). Qed.
Lemma lem5355221 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term651 _69725 _69726.
Proof. exact (@lem5355220 _69725 _69726 (@lem5355217 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355222 (_69725 : int) (_69726 : int) : (term652 _69725 _69726) = (term335 _69725 _69726).
Proof. exact (@lem1982733 (term335 _69725 _69726)). Qed.
Lemma lem5355223 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5355224 (_69725 : int) (_69726 : int) : (term653 _69725 _69726) = (term397 _69725 _69726).
Proof. exact (MK_COMB (@lem5355223) (@lem5355222 _69725 _69726)). Qed.
Lemma lem5355225 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5355226 (_69725 : int) (_69726 : int) : (term651 _69725 _69726) = (term398 _69725 _69726).
Proof. exact (MK_COMB (@lem5355224 _69725 _69726) (@lem5355225)). Qed.
Lemma lem5355227 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term398 _69725 _69726.
Proof. exact (EQ_MP (@lem5355226 _69725 _69726) (@lem5355221 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355229 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5355230 : term580 = term380.
Proof. exact (@lem5355229 term254 term267). Qed.
Lemma lem5355232 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355233 : term267 = term346.
Proof. exact (@lem5355232 term146). Qed.
Lemma lem5355235 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355236 : term254 = term309.
Proof. exact (@lem5355235 (NUMERAL 0)). Qed.
Lemma lem5355237 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5355238 : term581 = term582.
Proof. exact (MK_COMB (@lem5355237) (@lem5355236)). Qed.
Lemma lem5355239 : term380 = term583.
Proof. exact (MK_COMB (@lem5355238) (@lem5355233)). Qed.
Lemma lem5355240 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5355242 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355243 : term380 = term381.
Proof. exact (@lem5355242 (NUMERAL 0) term146). Qed.
Lemma lem5355244 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355245 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355246 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355245 h1) (fun h1 : term381 = True => @lem5355244)). Qed.
Lemma lem5355247 : term381 = True.
Proof. exact (EQ_MP (@lem5355246) (@lem5355244)). Qed.
Lemma lem5355248 : term380 = True.
Proof. exact (TRANS (@lem5355243) (@lem5355247)). Qed.
Lemma lem5355249 : True = term380.
Proof. exact (SYM (@lem5355248)). Qed.
Lemma lem5355250 : term380.
Proof. exact (EQ_MP (@lem5355249) (@lem0)). Qed.
Lemma lem5355251 : term585.
Proof. exact (@lem5355240 (@lem5355250)). Qed.
Lemma lem5355253 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355254 : term380 = term381.
Proof. exact (@lem5355253 (NUMERAL 0) term146). Qed.
Lemma lem5355255 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355256 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355257 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355256 h1) (fun h1 : term381 = True => @lem5355255)). Qed.
Lemma lem5355258 : term381 = True.
Proof. exact (EQ_MP (@lem5355257) (@lem5355255)). Qed.
Lemma lem5355259 : term380 = True.
Proof. exact (TRANS (@lem5355254) (@lem5355258)). Qed.
Lemma lem5355260 : True = term380.
Proof. exact (SYM (@lem5355259)). Qed.
Lemma lem5355261 : term380.
Proof. exact (EQ_MP (@lem5355260) (@lem0)). Qed.
Lemma lem5355262 : term583 = term586.
Proof. exact (@lem5355251 (@lem5355261)). Qed.
Lemma lem5355264 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355265 : term321 = term322.
Proof. exact (@lem5355264 term146 term146). Qed.
Lemma lem5355266 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355267 : term324 = term146.
Proof. exact (EQ_MP (@lem5355266) (@lem940073)). Qed.
Lemma lem5355268 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355269 : term322 = term267.
Proof. exact (MK_COMB (@lem5355268) (@lem5355267)). Qed.
Lemma lem5355270 : term321 = term267.
Proof. exact (TRANS (@lem5355265) (@lem5355269)). Qed.
Lemma lem5355272 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355273 : term392 = term254.
Proof. exact (@lem5355272 term146). Qed.
Lemma lem5355274 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5355275 : term587 = term581.
Proof. exact (MK_COMB (@lem5355274) (@lem5355273)). Qed.
Lemma lem5355276 : term586 = term380.
Proof. exact (MK_COMB (@lem5355275) (@lem5355270)). Qed.
Lemma lem5355278 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355279 : term380 = term381.
Proof. exact (@lem5355278 (NUMERAL 0) term146). Qed.
Lemma lem5355280 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355281 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355282 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355281 h1) (fun h1 : term381 = True => @lem5355280)). Qed.
Lemma lem5355283 : term381 = True.
Proof. exact (EQ_MP (@lem5355282) (@lem5355280)). Qed.
Lemma lem5355284 : term380 = True.
Proof. exact (TRANS (@lem5355279) (@lem5355283)). Qed.
Lemma lem5355285 : term586 = True.
Proof. exact (TRANS (@lem5355276) (@lem5355284)). Qed.
Lemma lem5355286 : term583 = True.
Proof. exact (TRANS (@lem5355262) (@lem5355285)). Qed.
Lemma lem5355287 : term380 = True.
Proof. exact (TRANS (@lem5355239) (@lem5355286)). Qed.
Lemma lem5355288 : term580 = True.
Proof. exact (TRANS (@lem5355230) (@lem5355287)). Qed.
Lemma lem5355289 : True = term580.
Proof. exact (SYM (@lem5355288)). Qed.
Lemma lem5355290 : term580.
Proof. exact (EQ_MP (@lem5355289) (@lem0)). Qed.
Lemma lem5355291 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term644 _69725 _69726.
Proof. exact (conj (@lem5355290) (@lem5355150 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355293 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5355294 (_69725 : int) (_69726 : int) : term645 _69725 _69726.
Proof. exact (@lem5355293 term267 (term361 _69725 _69726)). Qed.
Lemma lem5355295 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term646 _69725 _69726.
Proof. exact (@lem5355294 _69725 _69726 (@lem5355291 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355296 (_69725 : int) (_69726 : int) : (term647 _69725 _69726) = (term361 _69725 _69726).
Proof. exact (@lem1982733 (term361 _69725 _69726)). Qed.
Lemma lem5355297 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5355298 (_69725 : int) (_69726 : int) : (term648 _69725 _69726) = (term362 _69725 _69726).
Proof. exact (MK_COMB (@lem5355297) (@lem5355296 _69725 _69726)). Qed.
Lemma lem5355299 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5355300 (_69725 : int) (_69726 : int) : (term646 _69725 _69726) = (term363 _69725 _69726).
Proof. exact (MK_COMB (@lem5355298 _69725 _69726) (@lem5355299)). Qed.
Lemma lem5355301 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term363 _69725 _69726.
Proof. exact (EQ_MP (@lem5355300 _69725 _69726) (@lem5355295 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355302 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term449 _69725 _69726.
Proof. exact (conj (@lem5355301 _69724 _69725 _69726 h1) (@lem5355227 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355304 (x : real) (y : real) : term600 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5355305 (_69725 : int) (_69726 : int) : term664 _69725 _69726.
Proof. exact (@lem5355304 (term361 _69725 _69726) (term335 _69725 _69726)). Qed.
Lemma lem5355306 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term665 _69725 _69726.
Proof. exact (@lem5355305 _69725 _69726 (@lem5355302 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355307 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = (term667 _69725 _69726).
Proof. exact (@lem1982753 (term337 _69725) (real_of_int _69725) (term659 _69726) (term337 _69726)). Qed.
Lemma lem5355308 (_69725 : int) : (term605 _69725) = (term606 _69725).
Proof. exact (@lem1982713 term312 (real_of_int _69725)). Qed.
Lemma lem5355310 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355311 : term267 = term346.
Proof. exact (@lem5355310 term146). Qed.
Lemma lem5355313 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5355314 : term312 = term313.
Proof. exact (@lem5355313 term146). Qed.
Lemma lem5355315 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355316 : term607 = term608.
Proof. exact (MK_COMB (@lem5355315) (@lem5355314)). Qed.
Lemma lem5355317 : term609 = term610.
Proof. exact (MK_COMB (@lem5355316) (@lem5355311)). Qed.
Lemma lem5355318 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5355320 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355321 : term380 = term381.
Proof. exact (@lem5355320 (NUMERAL 0) term146). Qed.
Lemma lem5355322 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355323 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355324 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355323 h1) (fun h1 : term381 = True => @lem5355322)). Qed.
Lemma lem5355325 : term381 = True.
Proof. exact (EQ_MP (@lem5355324) (@lem5355322)). Qed.
Lemma lem5355326 : term380 = True.
Proof. exact (TRANS (@lem5355321) (@lem5355325)). Qed.
Lemma lem5355327 : True = term380.
Proof. exact (SYM (@lem5355326)). Qed.
Lemma lem5355328 : term380.
Proof. exact (EQ_MP (@lem5355327) (@lem0)). Qed.
Lemma lem5355329 : term612.
Proof. exact (@lem5355318 (@lem5355328)). Qed.
Lemma lem5355331 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355332 : term380 = term381.
Proof. exact (@lem5355331 (NUMERAL 0) term146). Qed.
Lemma lem5355333 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355334 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355335 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355334 h1) (fun h1 : term381 = True => @lem5355333)). Qed.
Lemma lem5355336 : term381 = True.
Proof. exact (EQ_MP (@lem5355335) (@lem5355333)). Qed.
Lemma lem5355337 : term380 = True.
Proof. exact (TRANS (@lem5355332) (@lem5355336)). Qed.
Lemma lem5355338 : True = term380.
Proof. exact (SYM (@lem5355337)). Qed.
Lemma lem5355339 : term380.
Proof. exact (EQ_MP (@lem5355338) (@lem0)). Qed.
Lemma lem5355340 : term613.
Proof. exact (@lem5355329 (@lem5355339)). Qed.
Lemma lem5355342 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355343 : term380 = term381.
Proof. exact (@lem5355342 (NUMERAL 0) term146). Qed.
Lemma lem5355344 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355345 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355346 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355345 h1) (fun h1 : term381 = True => @lem5355344)). Qed.
Lemma lem5355347 : term381 = True.
Proof. exact (EQ_MP (@lem5355346) (@lem5355344)). Qed.
Lemma lem5355348 : term380 = True.
Proof. exact (TRANS (@lem5355343) (@lem5355347)). Qed.
Lemma lem5355349 : True = term380.
Proof. exact (SYM (@lem5355348)). Qed.
Lemma lem5355350 : term380.
Proof. exact (EQ_MP (@lem5355349) (@lem0)). Qed.
Lemma lem5355351 : term614.
Proof. exact (@lem5355340 (@lem5355350)). Qed.
Lemma lem5355353 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355354 : term321 = term322.
Proof. exact (@lem5355353 term146 term146). Qed.
Lemma lem5355355 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355356 : term324 = term146.
Proof. exact (EQ_MP (@lem5355355) (@lem940073)). Qed.
Lemma lem5355357 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355358 : term322 = term267.
Proof. exact (MK_COMB (@lem5355357) (@lem5355356)). Qed.
Lemma lem5355359 : term321 = term267.
Proof. exact (TRANS (@lem5355354) (@lem5355358)). Qed.
Lemma lem5355361 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5355362 : term347 = term352.
Proof. exact (@lem5355361 term146 term146). Qed.
Lemma lem5355363 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355364 : term324 = term146.
Proof. exact (EQ_MP (@lem5355363) (@lem940073)). Qed.
Lemma lem5355365 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355366 : term322 = term267.
Proof. exact (MK_COMB (@lem5355365) (@lem5355364)). Qed.
Lemma lem5355367 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5355368 : term352 = term312.
Proof. exact (MK_COMB (@lem5355367) (@lem5355366)). Qed.
Lemma lem5355369 : term347 = term312.
Proof. exact (TRANS (@lem5355362) (@lem5355368)). Qed.
Lemma lem5355370 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355371 : term615 = term607.
Proof. exact (MK_COMB (@lem5355370) (@lem5355369)). Qed.
Lemma lem5355372 : term616 = term609.
Proof. exact (MK_COMB (@lem5355371) (@lem5355359)). Qed.
Lemma lem5355374 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5355375 : term609 = term254.
Proof. exact (@lem5355374 term146). Qed.
Lemma lem5355376 : term616 = term254.
Proof. exact (TRANS (@lem5355372) (@lem5355375)). Qed.
Lemma lem5355377 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5355378 : term618 = term390.
Proof. exact (MK_COMB (@lem5355377) (@lem5355376)). Qed.
Lemma lem5355379 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5355380 : term619 = term392.
Proof. exact (MK_COMB (@lem5355378) (@lem5355379)). Qed.
Lemma lem5355382 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355383 : term392 = term254.
Proof. exact (@lem5355382 term146). Qed.
Lemma lem5355384 : term619 = term254.
Proof. exact (TRANS (@lem5355380) (@lem5355383)). Qed.
Lemma lem5355386 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355387 : term321 = term322.
Proof. exact (@lem5355386 term146 term146). Qed.
Lemma lem5355388 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355389 : term324 = term146.
Proof. exact (EQ_MP (@lem5355388) (@lem940073)). Qed.
Lemma lem5355390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355391 : term322 = term267.
Proof. exact (MK_COMB (@lem5355390) (@lem5355389)). Qed.
Lemma lem5355392 : term321 = term267.
Proof. exact (TRANS (@lem5355387) (@lem5355391)). Qed.
Lemma lem5355393 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5355394 : term394 = term392.
Proof. exact (MK_COMB (@lem5355393) (@lem5355392)). Qed.
Lemma lem5355396 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355397 : term392 = term254.
Proof. exact (@lem5355396 term146). Qed.
Lemma lem5355398 : term394 = term254.
Proof. exact (TRANS (@lem5355394) (@lem5355397)). Qed.
Lemma lem5355399 : term254 = term394.
Proof. exact (SYM (@lem5355398)). Qed.
Lemma lem5355400 : term619 = term394.
Proof. exact (TRANS (@lem5355384) (@lem5355399)). Qed.
Lemma lem5355401 : term610 = term309.
Proof. exact (@lem5355351 (@lem5355400)). Qed.
Lemma lem5355402 : term609 = term309.
Proof. exact (TRANS (@lem5355317) (@lem5355401)). Qed.
Lemma lem5355404 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5355405 : term309 = term254.
Proof. exact (@lem5355404 term254). Qed.
Lemma lem5355406 : term609 = term254.
Proof. exact (TRANS (@lem5355402) (@lem5355405)). Qed.
Lemma lem5355407 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5355408 : term620 = term390.
Proof. exact (MK_COMB (@lem5355407) (@lem5355406)). Qed.
Lemma lem5355409 (_69725 : int) : (real_of_int _69725) = (real_of_int _69725).
Proof. exact (eq_refl (real_of_int _69725)). Qed.
Lemma lem5355410 (_69725 : int) : (term606 _69725) = (term621 _69725).
Proof. exact (MK_COMB (@lem5355408) (@lem5355409 _69725)). Qed.
Lemma lem5355411 (_69725 : int) : (term605 _69725) = (term621 _69725).
Proof. exact (TRANS (@lem5355308 _69725) (@lem5355410 _69725)). Qed.
Lemma lem5355412 (_69725 : int) : (term621 _69725) = term254.
Proof. exact (@lem1982719 (real_of_int _69725)). Qed.
Lemma lem5355413 (_69725 : int) : (term605 _69725) = term254.
Proof. exact (TRANS (@lem5355411 _69725) (@lem5355412 _69725)). Qed.
Lemma lem5355414 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355415 (_69725 : int) : (term622 _69725) = term623.
Proof. exact (MK_COMB (@lem5355414) (@lem5355413 _69725)). Qed.
Lemma lem5355416 (_69726 : int) : (term668 _69726) = (term625 _69726).
Proof. exact (@lem1982759 (real_of_int _69726) (term337 _69726) term312). Qed.
Lemma lem5355417 (_69726 : int) : (term626 _69726) = (term606 _69726).
Proof. exact (@lem1982715 term312 (real_of_int _69726)). Qed.
Lemma lem5355419 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355420 : term267 = term346.
Proof. exact (@lem5355419 term146). Qed.
Lemma lem5355422 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5355423 : term312 = term313.
Proof. exact (@lem5355422 term146). Qed.
Lemma lem5355424 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355425 : term607 = term608.
Proof. exact (MK_COMB (@lem5355424) (@lem5355423)). Qed.
Lemma lem5355426 : term609 = term610.
Proof. exact (MK_COMB (@lem5355425) (@lem5355420)). Qed.
Lemma lem5355427 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5355429 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355430 : term380 = term381.
Proof. exact (@lem5355429 (NUMERAL 0) term146). Qed.
Lemma lem5355431 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355432 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355433 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355432 h1) (fun h1 : term381 = True => @lem5355431)). Qed.
Lemma lem5355434 : term381 = True.
Proof. exact (EQ_MP (@lem5355433) (@lem5355431)). Qed.
Lemma lem5355435 : term380 = True.
Proof. exact (TRANS (@lem5355430) (@lem5355434)). Qed.
Lemma lem5355436 : True = term380.
Proof. exact (SYM (@lem5355435)). Qed.
Lemma lem5355437 : term380.
Proof. exact (EQ_MP (@lem5355436) (@lem0)). Qed.
Lemma lem5355438 : term612.
Proof. exact (@lem5355427 (@lem5355437)). Qed.
Lemma lem5355440 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355441 : term380 = term381.
Proof. exact (@lem5355440 (NUMERAL 0) term146). Qed.
Lemma lem5355442 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355443 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355444 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355443 h1) (fun h1 : term381 = True => @lem5355442)). Qed.
Lemma lem5355445 : term381 = True.
Proof. exact (EQ_MP (@lem5355444) (@lem5355442)). Qed.
Lemma lem5355446 : term380 = True.
Proof. exact (TRANS (@lem5355441) (@lem5355445)). Qed.
Lemma lem5355447 : True = term380.
Proof. exact (SYM (@lem5355446)). Qed.
Lemma lem5355448 : term380.
Proof. exact (EQ_MP (@lem5355447) (@lem0)). Qed.
Lemma lem5355449 : term613.
Proof. exact (@lem5355438 (@lem5355448)). Qed.
Lemma lem5355451 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355452 : term380 = term381.
Proof. exact (@lem5355451 (NUMERAL 0) term146). Qed.
Lemma lem5355453 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355454 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355455 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355454 h1) (fun h1 : term381 = True => @lem5355453)). Qed.
Lemma lem5355456 : term381 = True.
Proof. exact (EQ_MP (@lem5355455) (@lem5355453)). Qed.
Lemma lem5355457 : term380 = True.
Proof. exact (TRANS (@lem5355452) (@lem5355456)). Qed.
Lemma lem5355458 : True = term380.
Proof. exact (SYM (@lem5355457)). Qed.
Lemma lem5355459 : term380.
Proof. exact (EQ_MP (@lem5355458) (@lem0)). Qed.
Lemma lem5355460 : term614.
Proof. exact (@lem5355449 (@lem5355459)). Qed.
Lemma lem5355462 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355463 : term321 = term322.
Proof. exact (@lem5355462 term146 term146). Qed.
Lemma lem5355464 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355465 : term324 = term146.
Proof. exact (EQ_MP (@lem5355464) (@lem940073)). Qed.
Lemma lem5355466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355467 : term322 = term267.
Proof. exact (MK_COMB (@lem5355466) (@lem5355465)). Qed.
Lemma lem5355468 : term321 = term267.
Proof. exact (TRANS (@lem5355463) (@lem5355467)). Qed.
Lemma lem5355470 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5355471 : term347 = term352.
Proof. exact (@lem5355470 term146 term146). Qed.
Lemma lem5355472 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355473 : term324 = term146.
Proof. exact (EQ_MP (@lem5355472) (@lem940073)). Qed.
Lemma lem5355474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355475 : term322 = term267.
Proof. exact (MK_COMB (@lem5355474) (@lem5355473)). Qed.
Lemma lem5355476 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5355477 : term352 = term312.
Proof. exact (MK_COMB (@lem5355476) (@lem5355475)). Qed.
Lemma lem5355478 : term347 = term312.
Proof. exact (TRANS (@lem5355471) (@lem5355477)). Qed.
Lemma lem5355479 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355480 : term615 = term607.
Proof. exact (MK_COMB (@lem5355479) (@lem5355478)). Qed.
Lemma lem5355481 : term616 = term609.
Proof. exact (MK_COMB (@lem5355480) (@lem5355468)). Qed.
Lemma lem5355483 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5355484 : term609 = term254.
Proof. exact (@lem5355483 term146). Qed.
Lemma lem5355485 : term616 = term254.
Proof. exact (TRANS (@lem5355481) (@lem5355484)). Qed.
Lemma lem5355486 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5355487 : term618 = term390.
Proof. exact (MK_COMB (@lem5355486) (@lem5355485)). Qed.
Lemma lem5355488 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5355489 : term619 = term392.
Proof. exact (MK_COMB (@lem5355487) (@lem5355488)). Qed.
Lemma lem5355491 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355492 : term392 = term254.
Proof. exact (@lem5355491 term146). Qed.
Lemma lem5355493 : term619 = term254.
Proof. exact (TRANS (@lem5355489) (@lem5355492)). Qed.
Lemma lem5355495 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355496 : term321 = term322.
Proof. exact (@lem5355495 term146 term146). Qed.
Lemma lem5355497 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355498 : term324 = term146.
Proof. exact (EQ_MP (@lem5355497) (@lem940073)). Qed.
Lemma lem5355499 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355500 : term322 = term267.
Proof. exact (MK_COMB (@lem5355499) (@lem5355498)). Qed.
Lemma lem5355501 : term321 = term267.
Proof. exact (TRANS (@lem5355496) (@lem5355500)). Qed.
Lemma lem5355502 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5355503 : term394 = term392.
Proof. exact (MK_COMB (@lem5355502) (@lem5355501)). Qed.
Lemma lem5355505 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355506 : term392 = term254.
Proof. exact (@lem5355505 term146). Qed.
Lemma lem5355507 : term394 = term254.
Proof. exact (TRANS (@lem5355503) (@lem5355506)). Qed.
Lemma lem5355508 : term254 = term394.
Proof. exact (SYM (@lem5355507)). Qed.
Lemma lem5355509 : term619 = term394.
Proof. exact (TRANS (@lem5355493) (@lem5355508)). Qed.
Lemma lem5355510 : term610 = term309.
Proof. exact (@lem5355460 (@lem5355509)). Qed.
Lemma lem5355511 : term609 = term309.
Proof. exact (TRANS (@lem5355426) (@lem5355510)). Qed.
Lemma lem5355513 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5355514 : term309 = term254.
Proof. exact (@lem5355513 term254). Qed.
Lemma lem5355515 : term609 = term254.
Proof. exact (TRANS (@lem5355511) (@lem5355514)). Qed.
Lemma lem5355516 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5355517 : term620 = term390.
Proof. exact (MK_COMB (@lem5355516) (@lem5355515)). Qed.
Lemma lem5355518 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5355519 (_69726 : int) : (term606 _69726) = (term621 _69726).
Proof. exact (MK_COMB (@lem5355517) (@lem5355518 _69726)). Qed.
Lemma lem5355520 (_69726 : int) : (term626 _69726) = (term621 _69726).
Proof. exact (TRANS (@lem5355417 _69726) (@lem5355519 _69726)). Qed.
Lemma lem5355521 (_69726 : int) : (term621 _69726) = term254.
Proof. exact (@lem1982719 (real_of_int _69726)). Qed.
Lemma lem5355522 (_69726 : int) : (term626 _69726) = term254.
Proof. exact (TRANS (@lem5355520 _69726) (@lem5355521 _69726)). Qed.
Lemma lem5355523 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355524 (_69726 : int) : (term627 _69726) = term623.
Proof. exact (MK_COMB (@lem5355523) (@lem5355522 _69726)). Qed.
Lemma lem5355525 : term312 = term312.
Proof. exact (eq_refl term312). Qed.
Lemma lem5355526 (_69726 : int) : (term625 _69726) = term628.
Proof. exact (MK_COMB (@lem5355524 _69726) (@lem5355525)). Qed.
Lemma lem5355527 (_69726 : int) : (term668 _69726) = term628.
Proof. exact (TRANS (@lem5355416 _69726) (@lem5355526 _69726)). Qed.
Lemma lem5355528 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5355529 (_69726 : int) : (term668 _69726) = term312.
Proof. exact (TRANS (@lem5355527 _69726) (@lem5355528)). Qed.
Lemma lem5355530 (_69725 : int) (_69726 : int) : (term667 _69725 _69726) = term628.
Proof. exact (MK_COMB (@lem5355415 _69725) (@lem5355529 _69726)). Qed.
Lemma lem5355531 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = term628.
Proof. exact (TRANS (@lem5355307 _69725 _69726) (@lem5355530 _69725 _69726)). Qed.
Lemma lem5355532 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5355533 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = term312.
Proof. exact (TRANS (@lem5355531 _69725 _69726) (@lem5355532)). Qed.
Lemma lem5355534 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5355535 (_69725 : int) (_69726 : int) : (term669 _69725 _69726) = term630.
Proof. exact (MK_COMB (@lem5355534) (@lem5355533 _69725 _69726)). Qed.
Lemma lem5355536 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5355537 (_69725 : int) (_69726 : int) : (term665 _69725 _69726) = term631.
Proof. exact (MK_COMB (@lem5355535 _69725 _69726) (@lem5355536)). Qed.
Lemma lem5355538 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : term631.
Proof. exact (EQ_MP (@lem5355537 _69725 _69726) (@lem5355306 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355540 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5355541 : term631 = term632.
Proof. exact (@lem5355540 term254 term312). Qed.
Lemma lem5355543 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5355544 : term312 = term313.
Proof. exact (@lem5355543 term146). Qed.
Lemma lem5355546 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355547 : term254 = term309.
Proof. exact (@lem5355546 (NUMERAL 0)). Qed.
Lemma lem5355548 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5355549 : term256 = term633.
Proof. exact (MK_COMB (@lem5355548) (@lem5355547)). Qed.
Lemma lem5355550 : term632 = term634.
Proof. exact (MK_COMB (@lem5355549) (@lem5355544)). Qed.
Lemma lem5355551 : term635.
Proof. exact (@lem1980026 term254 term267 term312 term267). Qed.
Lemma lem5355553 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355554 : term380 = term381.
Proof. exact (@lem5355553 (NUMERAL 0) term146). Qed.
Lemma lem5355555 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355556 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355557 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355556 h1) (fun h1 : term381 = True => @lem5355555)). Qed.
Lemma lem5355558 : term381 = True.
Proof. exact (EQ_MP (@lem5355557) (@lem5355555)). Qed.
Lemma lem5355559 : term380 = True.
Proof. exact (TRANS (@lem5355554) (@lem5355558)). Qed.
Lemma lem5355560 : True = term380.
Proof. exact (SYM (@lem5355559)). Qed.
Lemma lem5355561 : term380.
Proof. exact (EQ_MP (@lem5355560) (@lem0)). Qed.
Lemma lem5355562 : term636.
Proof. exact (@lem5355551 (@lem5355561)). Qed.
Lemma lem5355564 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355565 : term380 = term381.
Proof. exact (@lem5355564 (NUMERAL 0) term146). Qed.
Lemma lem5355566 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355567 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355568 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355567 h1) (fun h1 : term381 = True => @lem5355566)). Qed.
Lemma lem5355569 : term381 = True.
Proof. exact (EQ_MP (@lem5355568) (@lem5355566)). Qed.
Lemma lem5355570 : term380 = True.
Proof. exact (TRANS (@lem5355565) (@lem5355569)). Qed.
Lemma lem5355571 : True = term380.
Proof. exact (SYM (@lem5355570)). Qed.
Lemma lem5355572 : term380.
Proof. exact (EQ_MP (@lem5355571) (@lem0)). Qed.
Lemma lem5355573 : term634 = term637.
Proof. exact (@lem5355562 (@lem5355572)). Qed.
Lemma lem5355575 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5355576 : term347 = term352.
Proof. exact (@lem5355575 term146 term146). Qed.
Lemma lem5355577 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355578 : term324 = term146.
Proof. exact (EQ_MP (@lem5355577) (@lem940073)). Qed.
Lemma lem5355579 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355580 : term322 = term267.
Proof. exact (MK_COMB (@lem5355579) (@lem5355578)). Qed.
Lemma lem5355581 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5355582 : term352 = term312.
Proof. exact (MK_COMB (@lem5355581) (@lem5355580)). Qed.
Lemma lem5355583 : term347 = term312.
Proof. exact (TRANS (@lem5355576) (@lem5355582)). Qed.
Lemma lem5355585 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355586 : term392 = term254.
Proof. exact (@lem5355585 term146). Qed.
Lemma lem5355587 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5355588 : term638 = term256.
Proof. exact (MK_COMB (@lem5355587) (@lem5355586)). Qed.
Lemma lem5355589 : term637 = term632.
Proof. exact (MK_COMB (@lem5355588) (@lem5355583)). Qed.
Lemma lem5355591 (m : nat) (n : nat) : (term639 m n) = (term640 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5355592 : term632 = term641.
Proof. exact (@lem5355591 (NUMERAL 0) term146). Qed.
Lemma lem5355593 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355594 (h1 : term382 = (BIT1 0)) : (term146 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5355595 : (term382 = (BIT1 0)) = ((term146 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355594 h1) (fun h1 : (term146 = (NUMERAL 0)) = False => @lem5355593)). Qed.
Lemma lem5355596 : (term146 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5355595) (@lem5355593)). Qed.
Lemma lem5355597 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5355598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5355599 : term642 = (and True).
Proof. exact (MK_COMB (@lem5355598) (@lem5355597)). Qed.
Lemma lem5355600 : term641 = (True /\ False).
Proof. exact (MK_COMB (@lem5355599) (@lem5355596)). Qed.
Lemma lem5355602 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5355603 : term641 = False.
Proof. exact (TRANS (@lem5355600) (@lem5355602)). Qed.
Lemma lem5355604 : term632 = False.
Proof. exact (TRANS (@lem5355592) (@lem5355603)). Qed.
Lemma lem5355605 : term637 = False.
Proof. exact (TRANS (@lem5355589) (@lem5355604)). Qed.
Lemma lem5355606 : term634 = False.
Proof. exact (TRANS (@lem5355573) (@lem5355605)). Qed.
Lemma lem5355607 : term632 = False.
Proof. exact (TRANS (@lem5355550) (@lem5355606)). Qed.
Lemma lem5355608 : term631 = False.
Proof. exact (TRANS (@lem5355541) (@lem5355607)). Qed.
Lemma lem5355609 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term670 _69724 _69725 _69726) : False.
Proof. exact (EQ_MP (@lem5355608) (@lem5355538 _69724 _69725 _69726 h1)). Qed.
Lemma lem5355610 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term566 _69724 _69725 _69726) : False.
Proof. exact (or_elim (@lem5354667 _69724 _69725 _69726 h1) (fun h0 : term663 _69724 _69725 _69726 => @lem5355138 _69724 _69725 _69726 h0) (fun h0 : term670 _69724 _69725 _69726 => @lem5355609 _69724 _69725 _69726 h0)). Qed.
Lemma lem5355611 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term575 _69724 _69725 _69726) : False.
Proof. exact (or_elim (@lem5353722 _69724 _69725 _69726 h1) (fun h0 : term570 _69724 _69725 _69726 => @lem5354666 _69724 _69725 _69726 h0) (fun h0 : term566 _69724 _69725 _69726 => @lem5355610 _69724 _69725 _69726 h0)). Qed.
Lemma lem5355612 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term562 _69724 _69725 _69726) : term562 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5355613 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term557 _69725 _69724 _69726) : term557 _69725 _69724 _69726.
Proof. exact (h1). Qed.
Lemma lem5355614 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term671 _69725 _69724 _69726.
Proof. exact (h1). Qed.
Lemma lem5355615 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term558 _69725 _69724 _69726.
Proof. exact (proj2 (@lem5355614 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355617 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term527 _69725 _69724 _69726.
Proof. exact (proj2 (@lem5355615 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355619 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term496 _69725 _69724 _69726.
Proof. exact (proj2 (@lem5355617 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355621 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term465 _69724 _69726.
Proof. exact (proj2 (@lem5355619 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355623 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term360 _69724 _69726.
Proof. exact (proj2 (@lem5355621 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355624 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : (term336 _69724 _69726) = term254.
Proof. exact (proj1 (@lem5355621 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355626 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5355627 : term580 = term380.
Proof. exact (@lem5355626 term254 term267). Qed.
Lemma lem5355629 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355630 : term267 = term346.
Proof. exact (@lem5355629 term146). Qed.
Lemma lem5355632 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355633 : term254 = term309.
Proof. exact (@lem5355632 (NUMERAL 0)). Qed.
Lemma lem5355634 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5355635 : term581 = term582.
Proof. exact (MK_COMB (@lem5355634) (@lem5355633)). Qed.
Lemma lem5355636 : term380 = term583.
Proof. exact (MK_COMB (@lem5355635) (@lem5355630)). Qed.
Lemma lem5355637 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5355639 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355640 : term380 = term381.
Proof. exact (@lem5355639 (NUMERAL 0) term146). Qed.
Lemma lem5355641 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355642 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355643 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355642 h1) (fun h1 : term381 = True => @lem5355641)). Qed.
Lemma lem5355644 : term381 = True.
Proof. exact (EQ_MP (@lem5355643) (@lem5355641)). Qed.
Lemma lem5355645 : term380 = True.
Proof. exact (TRANS (@lem5355640) (@lem5355644)). Qed.
Lemma lem5355646 : True = term380.
Proof. exact (SYM (@lem5355645)). Qed.
Lemma lem5355647 : term380.
Proof. exact (EQ_MP (@lem5355646) (@lem0)). Qed.
Lemma lem5355648 : term585.
Proof. exact (@lem5355637 (@lem5355647)). Qed.
Lemma lem5355650 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355651 : term380 = term381.
Proof. exact (@lem5355650 (NUMERAL 0) term146). Qed.
Lemma lem5355652 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355653 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355654 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355653 h1) (fun h1 : term381 = True => @lem5355652)). Qed.
Lemma lem5355655 : term381 = True.
Proof. exact (EQ_MP (@lem5355654) (@lem5355652)). Qed.
Lemma lem5355656 : term380 = True.
Proof. exact (TRANS (@lem5355651) (@lem5355655)). Qed.
Lemma lem5355657 : True = term380.
Proof. exact (SYM (@lem5355656)). Qed.
Lemma lem5355658 : term380.
Proof. exact (EQ_MP (@lem5355657) (@lem0)). Qed.
Lemma lem5355659 : term583 = term586.
Proof. exact (@lem5355648 (@lem5355658)). Qed.
Lemma lem5355661 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355662 : term321 = term322.
Proof. exact (@lem5355661 term146 term146). Qed.
Lemma lem5355663 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355664 : term324 = term146.
Proof. exact (EQ_MP (@lem5355663) (@lem940073)). Qed.
Lemma lem5355665 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355666 : term322 = term267.
Proof. exact (MK_COMB (@lem5355665) (@lem5355664)). Qed.
Lemma lem5355667 : term321 = term267.
Proof. exact (TRANS (@lem5355662) (@lem5355666)). Qed.
Lemma lem5355669 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355670 : term392 = term254.
Proof. exact (@lem5355669 term146). Qed.
Lemma lem5355671 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5355672 : term587 = term581.
Proof. exact (MK_COMB (@lem5355671) (@lem5355670)). Qed.
Lemma lem5355673 : term586 = term380.
Proof. exact (MK_COMB (@lem5355672) (@lem5355667)). Qed.
Lemma lem5355675 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355676 : term380 = term381.
Proof. exact (@lem5355675 (NUMERAL 0) term146). Qed.
Lemma lem5355677 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355678 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355679 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355678 h1) (fun h1 : term381 = True => @lem5355677)). Qed.
Lemma lem5355680 : term381 = True.
Proof. exact (EQ_MP (@lem5355679) (@lem5355677)). Qed.
Lemma lem5355681 : term380 = True.
Proof. exact (TRANS (@lem5355676) (@lem5355680)). Qed.
Lemma lem5355682 : term586 = True.
Proof. exact (TRANS (@lem5355673) (@lem5355681)). Qed.
Lemma lem5355683 : term583 = True.
Proof. exact (TRANS (@lem5355659) (@lem5355682)). Qed.
Lemma lem5355684 : term380 = True.
Proof. exact (TRANS (@lem5355636) (@lem5355683)). Qed.
Lemma lem5355685 : term580 = True.
Proof. exact (TRANS (@lem5355627) (@lem5355684)). Qed.
Lemma lem5355686 : True = term580.
Proof. exact (SYM (@lem5355685)). Qed.
Lemma lem5355687 : term580.
Proof. exact (EQ_MP (@lem5355686) (@lem0)). Qed.
Lemma lem5355688 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term588 _69724 _69726.
Proof. exact (conj (@lem5355687) (@lem5355623 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355690 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5355691 (_69724 : int) (_69726 : int) : term590 _69724 _69726.
Proof. exact (@lem5355690 term267 (term357 _69724 _69726)). Qed.
Lemma lem5355692 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term591 _69724 _69726.
Proof. exact (@lem5355691 _69724 _69726 (@lem5355688 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355693 (_69724 : int) (_69726 : int) : (term592 _69724 _69726) = (term357 _69724 _69726).
Proof. exact (@lem1982733 (term357 _69724 _69726)). Qed.
Lemma lem5355694 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5355695 (_69724 : int) (_69726 : int) : (term593 _69724 _69726) = (term359 _69724 _69726).
Proof. exact (MK_COMB (@lem5355694) (@lem5355693 _69724 _69726)). Qed.
Lemma lem5355696 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5355697 (_69724 : int) (_69726 : int) : (term591 _69724 _69726) = (term360 _69724 _69726).
Proof. exact (MK_COMB (@lem5355695 _69724 _69726) (@lem5355696)). Qed.
Lemma lem5355698 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term360 _69724 _69726.
Proof. exact (EQ_MP (@lem5355697 _69724 _69726) (@lem5355692 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355700 (y : real) : term672 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5355701 (_69724 : int) (_69726 : int) : term673 _69724 _69726.
Proof. exact (@lem5355700 (term336 _69724 _69726)). Qed.
Lemma lem5355702 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term674 _69724 _69726.
Proof. exact (@lem5355701 _69724 _69726 (@lem5355624 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355703 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term675 _69724 _69726.
Proof. exact (@lem5355702 _69725 _69724 _69726 h1 term267). Qed.
Lemma lem5355704 (_69724 : int) (_69726 : int) : (term675 _69724 _69726) = ((term597 _69724 _69726) = term254).
Proof. exact (eq_refl (term675 _69724 _69726)). Qed.
Lemma lem5355705 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : (term597 _69724 _69726) = term254.
Proof. exact (EQ_MP (@lem5355704 _69724 _69726) (@lem5355703 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355706 (_69724 : int) (_69726 : int) : (term597 _69724 _69726) = (term336 _69724 _69726).
Proof. exact (@lem1982733 (term336 _69724 _69726)). Qed.
Lemma lem5355707 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5355708 (_69724 : int) (_69726 : int) : (term676 _69724 _69726) = (term408 _69724 _69726).
Proof. exact (MK_COMB (@lem5355707) (@lem5355706 _69724 _69726)). Qed.
Lemma lem5355709 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5355710 (_69724 : int) (_69726 : int) : ((term597 _69724 _69726) = term254) = ((term336 _69724 _69726) = term254).
Proof. exact (MK_COMB (@lem5355708 _69724 _69726) (@lem5355709)). Qed.
Lemma lem5355711 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : (term336 _69724 _69726) = term254.
Proof. exact (EQ_MP (@lem5355710 _69724 _69726) (@lem5355705 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355712 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term465 _69724 _69726.
Proof. exact (conj (@lem5355711 _69725 _69724 _69726 h1) (@lem5355698 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355714 (x : real) (y : real) : term677 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5355715 (_69724 : int) (_69726 : int) : term678 _69724 _69726.
Proof. exact (@lem5355714 (term336 _69724 _69726) (term357 _69724 _69726)). Qed.
Lemma lem5355716 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term602 _69724 _69726.
Proof. exact (@lem5355715 _69724 _69726 (@lem5355712 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355717 (_69724 : int) (_69726 : int) : (term603 _69724 _69726) = (term604 _69724 _69726).
Proof. exact (@lem1982753 (term337 _69724) (real_of_int _69724) (real_of_int _69726) (term356 _69726)). Qed.
Lemma lem5355718 (_69724 : int) : (term605 _69724) = (term606 _69724).
Proof. exact (@lem1982713 term312 (real_of_int _69724)). Qed.
Lemma lem5355720 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355721 : term267 = term346.
Proof. exact (@lem5355720 term146). Qed.
Lemma lem5355723 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5355724 : term312 = term313.
Proof. exact (@lem5355723 term146). Qed.
Lemma lem5355725 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355726 : term607 = term608.
Proof. exact (MK_COMB (@lem5355725) (@lem5355724)). Qed.
Lemma lem5355727 : term609 = term610.
Proof. exact (MK_COMB (@lem5355726) (@lem5355721)). Qed.
Lemma lem5355728 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5355730 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355731 : term380 = term381.
Proof. exact (@lem5355730 (NUMERAL 0) term146). Qed.
Lemma lem5355732 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355733 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355734 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355733 h1) (fun h1 : term381 = True => @lem5355732)). Qed.
Lemma lem5355735 : term381 = True.
Proof. exact (EQ_MP (@lem5355734) (@lem5355732)). Qed.
Lemma lem5355736 : term380 = True.
Proof. exact (TRANS (@lem5355731) (@lem5355735)). Qed.
Lemma lem5355737 : True = term380.
Proof. exact (SYM (@lem5355736)). Qed.
Lemma lem5355738 : term380.
Proof. exact (EQ_MP (@lem5355737) (@lem0)). Qed.
Lemma lem5355739 : term612.
Proof. exact (@lem5355728 (@lem5355738)). Qed.
Lemma lem5355741 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355742 : term380 = term381.
Proof. exact (@lem5355741 (NUMERAL 0) term146). Qed.
Lemma lem5355743 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355744 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355745 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355744 h1) (fun h1 : term381 = True => @lem5355743)). Qed.
Lemma lem5355746 : term381 = True.
Proof. exact (EQ_MP (@lem5355745) (@lem5355743)). Qed.
Lemma lem5355747 : term380 = True.
Proof. exact (TRANS (@lem5355742) (@lem5355746)). Qed.
Lemma lem5355748 : True = term380.
Proof. exact (SYM (@lem5355747)). Qed.
Lemma lem5355749 : term380.
Proof. exact (EQ_MP (@lem5355748) (@lem0)). Qed.
Lemma lem5355750 : term613.
Proof. exact (@lem5355739 (@lem5355749)). Qed.
Lemma lem5355752 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355753 : term380 = term381.
Proof. exact (@lem5355752 (NUMERAL 0) term146). Qed.
Lemma lem5355754 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355755 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355756 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355755 h1) (fun h1 : term381 = True => @lem5355754)). Qed.
Lemma lem5355757 : term381 = True.
Proof. exact (EQ_MP (@lem5355756) (@lem5355754)). Qed.
Lemma lem5355758 : term380 = True.
Proof. exact (TRANS (@lem5355753) (@lem5355757)). Qed.
Lemma lem5355759 : True = term380.
Proof. exact (SYM (@lem5355758)). Qed.
Lemma lem5355760 : term380.
Proof. exact (EQ_MP (@lem5355759) (@lem0)). Qed.
Lemma lem5355761 : term614.
Proof. exact (@lem5355750 (@lem5355760)). Qed.
Lemma lem5355763 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355764 : term321 = term322.
Proof. exact (@lem5355763 term146 term146). Qed.
Lemma lem5355765 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355766 : term324 = term146.
Proof. exact (EQ_MP (@lem5355765) (@lem940073)). Qed.
Lemma lem5355767 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355768 : term322 = term267.
Proof. exact (MK_COMB (@lem5355767) (@lem5355766)). Qed.
Lemma lem5355769 : term321 = term267.
Proof. exact (TRANS (@lem5355764) (@lem5355768)). Qed.
Lemma lem5355771 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5355772 : term347 = term352.
Proof. exact (@lem5355771 term146 term146). Qed.
Lemma lem5355773 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355774 : term324 = term146.
Proof. exact (EQ_MP (@lem5355773) (@lem940073)). Qed.
Lemma lem5355775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355776 : term322 = term267.
Proof. exact (MK_COMB (@lem5355775) (@lem5355774)). Qed.
Lemma lem5355777 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5355778 : term352 = term312.
Proof. exact (MK_COMB (@lem5355777) (@lem5355776)). Qed.
Lemma lem5355779 : term347 = term312.
Proof. exact (TRANS (@lem5355772) (@lem5355778)). Qed.
Lemma lem5355780 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355781 : term615 = term607.
Proof. exact (MK_COMB (@lem5355780) (@lem5355779)). Qed.
Lemma lem5355782 : term616 = term609.
Proof. exact (MK_COMB (@lem5355781) (@lem5355769)). Qed.
Lemma lem5355784 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5355785 : term609 = term254.
Proof. exact (@lem5355784 term146). Qed.
Lemma lem5355786 : term616 = term254.
Proof. exact (TRANS (@lem5355782) (@lem5355785)). Qed.
Lemma lem5355787 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5355788 : term618 = term390.
Proof. exact (MK_COMB (@lem5355787) (@lem5355786)). Qed.
Lemma lem5355789 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5355790 : term619 = term392.
Proof. exact (MK_COMB (@lem5355788) (@lem5355789)). Qed.
Lemma lem5355792 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355793 : term392 = term254.
Proof. exact (@lem5355792 term146). Qed.
Lemma lem5355794 : term619 = term254.
Proof. exact (TRANS (@lem5355790) (@lem5355793)). Qed.
Lemma lem5355796 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355797 : term321 = term322.
Proof. exact (@lem5355796 term146 term146). Qed.
Lemma lem5355798 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355799 : term324 = term146.
Proof. exact (EQ_MP (@lem5355798) (@lem940073)). Qed.
Lemma lem5355800 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355801 : term322 = term267.
Proof. exact (MK_COMB (@lem5355800) (@lem5355799)). Qed.
Lemma lem5355802 : term321 = term267.
Proof. exact (TRANS (@lem5355797) (@lem5355801)). Qed.
Lemma lem5355803 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5355804 : term394 = term392.
Proof. exact (MK_COMB (@lem5355803) (@lem5355802)). Qed.
Lemma lem5355806 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355807 : term392 = term254.
Proof. exact (@lem5355806 term146). Qed.
Lemma lem5355808 : term394 = term254.
Proof. exact (TRANS (@lem5355804) (@lem5355807)). Qed.
Lemma lem5355809 : term254 = term394.
Proof. exact (SYM (@lem5355808)). Qed.
Lemma lem5355810 : term619 = term394.
Proof. exact (TRANS (@lem5355794) (@lem5355809)). Qed.
Lemma lem5355811 : term610 = term309.
Proof. exact (@lem5355761 (@lem5355810)). Qed.
Lemma lem5355812 : term609 = term309.
Proof. exact (TRANS (@lem5355727) (@lem5355811)). Qed.
Lemma lem5355814 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5355815 : term309 = term254.
Proof. exact (@lem5355814 term254). Qed.
Lemma lem5355816 : term609 = term254.
Proof. exact (TRANS (@lem5355812) (@lem5355815)). Qed.
Lemma lem5355817 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5355818 : term620 = term390.
Proof. exact (MK_COMB (@lem5355817) (@lem5355816)). Qed.
Lemma lem5355819 (_69724 : int) : (real_of_int _69724) = (real_of_int _69724).
Proof. exact (eq_refl (real_of_int _69724)). Qed.
Lemma lem5355820 (_69724 : int) : (term606 _69724) = (term621 _69724).
Proof. exact (MK_COMB (@lem5355818) (@lem5355819 _69724)). Qed.
Lemma lem5355821 (_69724 : int) : (term605 _69724) = (term621 _69724).
Proof. exact (TRANS (@lem5355718 _69724) (@lem5355820 _69724)). Qed.
Lemma lem5355822 (_69724 : int) : (term621 _69724) = term254.
Proof. exact (@lem1982719 (real_of_int _69724)). Qed.
Lemma lem5355823 (_69724 : int) : (term605 _69724) = term254.
Proof. exact (TRANS (@lem5355821 _69724) (@lem5355822 _69724)). Qed.
Lemma lem5355824 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355825 (_69724 : int) : (term622 _69724) = term623.
Proof. exact (MK_COMB (@lem5355824) (@lem5355823 _69724)). Qed.
Lemma lem5355826 (_69726 : int) : (term624 _69726) = (term625 _69726).
Proof. exact (@lem1982763 (real_of_int _69726) (term337 _69726) term312). Qed.
Lemma lem5355827 (_69726 : int) : (term626 _69726) = (term606 _69726).
Proof. exact (@lem1982715 term312 (real_of_int _69726)). Qed.
Lemma lem5355829 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355830 : term267 = term346.
Proof. exact (@lem5355829 term146). Qed.
Lemma lem5355832 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5355833 : term312 = term313.
Proof. exact (@lem5355832 term146). Qed.
Lemma lem5355834 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355835 : term607 = term608.
Proof. exact (MK_COMB (@lem5355834) (@lem5355833)). Qed.
Lemma lem5355836 : term609 = term610.
Proof. exact (MK_COMB (@lem5355835) (@lem5355830)). Qed.
Lemma lem5355837 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5355839 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355840 : term380 = term381.
Proof. exact (@lem5355839 (NUMERAL 0) term146). Qed.
Lemma lem5355841 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355842 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355843 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355842 h1) (fun h1 : term381 = True => @lem5355841)). Qed.
Lemma lem5355844 : term381 = True.
Proof. exact (EQ_MP (@lem5355843) (@lem5355841)). Qed.
Lemma lem5355845 : term380 = True.
Proof. exact (TRANS (@lem5355840) (@lem5355844)). Qed.
Lemma lem5355846 : True = term380.
Proof. exact (SYM (@lem5355845)). Qed.
Lemma lem5355847 : term380.
Proof. exact (EQ_MP (@lem5355846) (@lem0)). Qed.
Lemma lem5355848 : term612.
Proof. exact (@lem5355837 (@lem5355847)). Qed.
Lemma lem5355850 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355851 : term380 = term381.
Proof. exact (@lem5355850 (NUMERAL 0) term146). Qed.
Lemma lem5355852 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355853 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355854 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355853 h1) (fun h1 : term381 = True => @lem5355852)). Qed.
Lemma lem5355855 : term381 = True.
Proof. exact (EQ_MP (@lem5355854) (@lem5355852)). Qed.
Lemma lem5355856 : term380 = True.
Proof. exact (TRANS (@lem5355851) (@lem5355855)). Qed.
Lemma lem5355857 : True = term380.
Proof. exact (SYM (@lem5355856)). Qed.
Lemma lem5355858 : term380.
Proof. exact (EQ_MP (@lem5355857) (@lem0)). Qed.
Lemma lem5355859 : term613.
Proof. exact (@lem5355848 (@lem5355858)). Qed.
Lemma lem5355861 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355862 : term380 = term381.
Proof. exact (@lem5355861 (NUMERAL 0) term146). Qed.
Lemma lem5355863 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355864 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355865 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355864 h1) (fun h1 : term381 = True => @lem5355863)). Qed.
Lemma lem5355866 : term381 = True.
Proof. exact (EQ_MP (@lem5355865) (@lem5355863)). Qed.
Lemma lem5355867 : term380 = True.
Proof. exact (TRANS (@lem5355862) (@lem5355866)). Qed.
Lemma lem5355868 : True = term380.
Proof. exact (SYM (@lem5355867)). Qed.
Lemma lem5355869 : term380.
Proof. exact (EQ_MP (@lem5355868) (@lem0)). Qed.
Lemma lem5355870 : term614.
Proof. exact (@lem5355859 (@lem5355869)). Qed.
Lemma lem5355872 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355873 : term321 = term322.
Proof. exact (@lem5355872 term146 term146). Qed.
Lemma lem5355874 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355875 : term324 = term146.
Proof. exact (EQ_MP (@lem5355874) (@lem940073)). Qed.
Lemma lem5355876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355877 : term322 = term267.
Proof. exact (MK_COMB (@lem5355876) (@lem5355875)). Qed.
Lemma lem5355878 : term321 = term267.
Proof. exact (TRANS (@lem5355873) (@lem5355877)). Qed.
Lemma lem5355880 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5355881 : term347 = term352.
Proof. exact (@lem5355880 term146 term146). Qed.
Lemma lem5355882 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355883 : term324 = term146.
Proof. exact (EQ_MP (@lem5355882) (@lem940073)). Qed.
Lemma lem5355884 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355885 : term322 = term267.
Proof. exact (MK_COMB (@lem5355884) (@lem5355883)). Qed.
Lemma lem5355886 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5355887 : term352 = term312.
Proof. exact (MK_COMB (@lem5355886) (@lem5355885)). Qed.
Lemma lem5355888 : term347 = term312.
Proof. exact (TRANS (@lem5355881) (@lem5355887)). Qed.
Lemma lem5355889 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355890 : term615 = term607.
Proof. exact (MK_COMB (@lem5355889) (@lem5355888)). Qed.
Lemma lem5355891 : term616 = term609.
Proof. exact (MK_COMB (@lem5355890) (@lem5355878)). Qed.
Lemma lem5355893 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5355894 : term609 = term254.
Proof. exact (@lem5355893 term146). Qed.
Lemma lem5355895 : term616 = term254.
Proof. exact (TRANS (@lem5355891) (@lem5355894)). Qed.
Lemma lem5355896 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5355897 : term618 = term390.
Proof. exact (MK_COMB (@lem5355896) (@lem5355895)). Qed.
Lemma lem5355898 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5355899 : term619 = term392.
Proof. exact (MK_COMB (@lem5355897) (@lem5355898)). Qed.
Lemma lem5355901 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355902 : term392 = term254.
Proof. exact (@lem5355901 term146). Qed.
Lemma lem5355903 : term619 = term254.
Proof. exact (TRANS (@lem5355899) (@lem5355902)). Qed.
Lemma lem5355905 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5355906 : term321 = term322.
Proof. exact (@lem5355905 term146 term146). Qed.
Lemma lem5355907 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355908 : term324 = term146.
Proof. exact (EQ_MP (@lem5355907) (@lem940073)). Qed.
Lemma lem5355909 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355910 : term322 = term267.
Proof. exact (MK_COMB (@lem5355909) (@lem5355908)). Qed.
Lemma lem5355911 : term321 = term267.
Proof. exact (TRANS (@lem5355906) (@lem5355910)). Qed.
Lemma lem5355912 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5355913 : term394 = term392.
Proof. exact (MK_COMB (@lem5355912) (@lem5355911)). Qed.
Lemma lem5355915 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355916 : term392 = term254.
Proof. exact (@lem5355915 term146). Qed.
Lemma lem5355917 : term394 = term254.
Proof. exact (TRANS (@lem5355913) (@lem5355916)). Qed.
Lemma lem5355918 : term254 = term394.
Proof. exact (SYM (@lem5355917)). Qed.
Lemma lem5355919 : term619 = term394.
Proof. exact (TRANS (@lem5355903) (@lem5355918)). Qed.
Lemma lem5355920 : term610 = term309.
Proof. exact (@lem5355870 (@lem5355919)). Qed.
Lemma lem5355921 : term609 = term309.
Proof. exact (TRANS (@lem5355836) (@lem5355920)). Qed.
Lemma lem5355923 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5355924 : term309 = term254.
Proof. exact (@lem5355923 term254). Qed.
Lemma lem5355925 : term609 = term254.
Proof. exact (TRANS (@lem5355921) (@lem5355924)). Qed.
Lemma lem5355926 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5355927 : term620 = term390.
Proof. exact (MK_COMB (@lem5355926) (@lem5355925)). Qed.
Lemma lem5355928 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5355929 (_69726 : int) : (term606 _69726) = (term621 _69726).
Proof. exact (MK_COMB (@lem5355927) (@lem5355928 _69726)). Qed.
Lemma lem5355930 (_69726 : int) : (term626 _69726) = (term621 _69726).
Proof. exact (TRANS (@lem5355827 _69726) (@lem5355929 _69726)). Qed.
Lemma lem5355931 (_69726 : int) : (term621 _69726) = term254.
Proof. exact (@lem1982719 (real_of_int _69726)). Qed.
Lemma lem5355932 (_69726 : int) : (term626 _69726) = term254.
Proof. exact (TRANS (@lem5355930 _69726) (@lem5355931 _69726)). Qed.
Lemma lem5355933 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5355934 (_69726 : int) : (term627 _69726) = term623.
Proof. exact (MK_COMB (@lem5355933) (@lem5355932 _69726)). Qed.
Lemma lem5355935 : term312 = term312.
Proof. exact (eq_refl term312). Qed.
Lemma lem5355936 (_69726 : int) : (term625 _69726) = term628.
Proof. exact (MK_COMB (@lem5355934 _69726) (@lem5355935)). Qed.
Lemma lem5355937 (_69726 : int) : (term624 _69726) = term628.
Proof. exact (TRANS (@lem5355826 _69726) (@lem5355936 _69726)). Qed.
Lemma lem5355938 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5355939 (_69726 : int) : (term624 _69726) = term312.
Proof. exact (TRANS (@lem5355937 _69726) (@lem5355938)). Qed.
Lemma lem5355940 (_69724 : int) (_69726 : int) : (term604 _69724 _69726) = term628.
Proof. exact (MK_COMB (@lem5355825 _69724) (@lem5355939 _69726)). Qed.
Lemma lem5355941 (_69724 : int) (_69726 : int) : (term603 _69724 _69726) = term628.
Proof. exact (TRANS (@lem5355717 _69724 _69726) (@lem5355940 _69724 _69726)). Qed.
Lemma lem5355942 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5355943 (_69724 : int) (_69726 : int) : (term603 _69724 _69726) = term312.
Proof. exact (TRANS (@lem5355941 _69724 _69726) (@lem5355942)). Qed.
Lemma lem5355944 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5355945 (_69724 : int) (_69726 : int) : (term629 _69724 _69726) = term630.
Proof. exact (MK_COMB (@lem5355944) (@lem5355943 _69724 _69726)). Qed.
Lemma lem5355946 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5355947 (_69724 : int) (_69726 : int) : (term602 _69724 _69726) = term631.
Proof. exact (MK_COMB (@lem5355945 _69724 _69726) (@lem5355946)). Qed.
Lemma lem5355948 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : term631.
Proof. exact (EQ_MP (@lem5355947 _69724 _69726) (@lem5355716 _69725 _69724 _69726 h1)). Qed.
Lemma lem5355950 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5355951 : term631 = term632.
Proof. exact (@lem5355950 term254 term312). Qed.
Lemma lem5355953 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5355954 : term312 = term313.
Proof. exact (@lem5355953 term146). Qed.
Lemma lem5355956 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5355957 : term254 = term309.
Proof. exact (@lem5355956 (NUMERAL 0)). Qed.
Lemma lem5355958 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5355959 : term256 = term633.
Proof. exact (MK_COMB (@lem5355958) (@lem5355957)). Qed.
Lemma lem5355960 : term632 = term634.
Proof. exact (MK_COMB (@lem5355959) (@lem5355954)). Qed.
Lemma lem5355961 : term635.
Proof. exact (@lem1980026 term254 term267 term312 term267). Qed.
Lemma lem5355963 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355964 : term380 = term381.
Proof. exact (@lem5355963 (NUMERAL 0) term146). Qed.
Lemma lem5355965 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355966 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355967 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355966 h1) (fun h1 : term381 = True => @lem5355965)). Qed.
Lemma lem5355968 : term381 = True.
Proof. exact (EQ_MP (@lem5355967) (@lem5355965)). Qed.
Lemma lem5355969 : term380 = True.
Proof. exact (TRANS (@lem5355964) (@lem5355968)). Qed.
Lemma lem5355970 : True = term380.
Proof. exact (SYM (@lem5355969)). Qed.
Lemma lem5355971 : term380.
Proof. exact (EQ_MP (@lem5355970) (@lem0)). Qed.
Lemma lem5355972 : term636.
Proof. exact (@lem5355961 (@lem5355971)). Qed.
Lemma lem5355974 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5355975 : term380 = term381.
Proof. exact (@lem5355974 (NUMERAL 0) term146). Qed.
Lemma lem5355976 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5355977 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5355978 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5355977 h1) (fun h1 : term381 = True => @lem5355976)). Qed.
Lemma lem5355979 : term381 = True.
Proof. exact (EQ_MP (@lem5355978) (@lem5355976)). Qed.
Lemma lem5355980 : term380 = True.
Proof. exact (TRANS (@lem5355975) (@lem5355979)). Qed.
Lemma lem5355981 : True = term380.
Proof. exact (SYM (@lem5355980)). Qed.
Lemma lem5355982 : term380.
Proof. exact (EQ_MP (@lem5355981) (@lem0)). Qed.
Lemma lem5355983 : term634 = term637.
Proof. exact (@lem5355972 (@lem5355982)). Qed.
Lemma lem5355985 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5355986 : term347 = term352.
Proof. exact (@lem5355985 term146 term146). Qed.
Lemma lem5355987 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5355988 : term324 = term146.
Proof. exact (EQ_MP (@lem5355987) (@lem940073)). Qed.
Lemma lem5355989 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5355990 : term322 = term267.
Proof. exact (MK_COMB (@lem5355989) (@lem5355988)). Qed.
Lemma lem5355991 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5355992 : term352 = term312.
Proof. exact (MK_COMB (@lem5355991) (@lem5355990)). Qed.
Lemma lem5355993 : term347 = term312.
Proof. exact (TRANS (@lem5355986) (@lem5355992)). Qed.
Lemma lem5355995 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5355996 : term392 = term254.
Proof. exact (@lem5355995 term146). Qed.
Lemma lem5355997 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5355998 : term638 = term256.
Proof. exact (MK_COMB (@lem5355997) (@lem5355996)). Qed.
Lemma lem5355999 : term637 = term632.
Proof. exact (MK_COMB (@lem5355998) (@lem5355993)). Qed.
Lemma lem5356001 (m : nat) (n : nat) : (term639 m n) = (term640 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5356002 : term632 = term641.
Proof. exact (@lem5356001 (NUMERAL 0) term146). Qed.
Lemma lem5356003 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356004 (h1 : term382 = (BIT1 0)) : (term146 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5356005 : (term382 = (BIT1 0)) = ((term146 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356004 h1) (fun h1 : (term146 = (NUMERAL 0)) = False => @lem5356003)). Qed.
Lemma lem5356006 : (term146 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5356005) (@lem5356003)). Qed.
Lemma lem5356007 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5356008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5356009 : term642 = (and True).
Proof. exact (MK_COMB (@lem5356008) (@lem5356007)). Qed.
Lemma lem5356010 : term641 = (True /\ False).
Proof. exact (MK_COMB (@lem5356009) (@lem5356006)). Qed.
Lemma lem5356012 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5356013 : term641 = False.
Proof. exact (TRANS (@lem5356010) (@lem5356012)). Qed.
Lemma lem5356014 : term632 = False.
Proof. exact (TRANS (@lem5356002) (@lem5356013)). Qed.
Lemma lem5356015 : term637 = False.
Proof. exact (TRANS (@lem5355999) (@lem5356014)). Qed.
Lemma lem5356016 : term634 = False.
Proof. exact (TRANS (@lem5355983) (@lem5356015)). Qed.
Lemma lem5356017 : term632 = False.
Proof. exact (TRANS (@lem5355960) (@lem5356016)). Qed.
Lemma lem5356018 : term631 = False.
Proof. exact (TRANS (@lem5355951) (@lem5356017)). Qed.
Lemma lem5356019 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term671 _69725 _69724 _69726) : False.
Proof. exact (EQ_MP (@lem5356018) (@lem5355948 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356020 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term679 _69725 _69724 _69726.
Proof. exact (h1). Qed.
Lemma lem5356021 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term559 _69725 _69724 _69726.
Proof. exact (proj2 (@lem5356020 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356023 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term528 _69725 _69724 _69726.
Proof. exact (proj2 (@lem5356021 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356025 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term497 _69725 _69724 _69726.
Proof. exact (proj2 (@lem5356023 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356027 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term466 _69725 _69724 _69726.
Proof. exact (proj2 (@lem5356025 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356029 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term360 _69724 _69726.
Proof. exact (proj2 (@lem5356027 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356030 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term410 _69724 _69725 _69726.
Proof. exact (proj1 (@lem5356027 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356032 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term363 _69724 _69726.
Proof. exact (proj1 (@lem5356030 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356034 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5356035 : term580 = term380.
Proof. exact (@lem5356034 term254 term267). Qed.
Lemma lem5356037 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356038 : term267 = term346.
Proof. exact (@lem5356037 term146). Qed.
Lemma lem5356040 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356041 : term254 = term309.
Proof. exact (@lem5356040 (NUMERAL 0)). Qed.
Lemma lem5356042 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5356043 : term581 = term582.
Proof. exact (MK_COMB (@lem5356042) (@lem5356041)). Qed.
Lemma lem5356044 : term380 = term583.
Proof. exact (MK_COMB (@lem5356043) (@lem5356038)). Qed.
Lemma lem5356045 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5356047 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356048 : term380 = term381.
Proof. exact (@lem5356047 (NUMERAL 0) term146). Qed.
Lemma lem5356049 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356050 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356051 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356050 h1) (fun h1 : term381 = True => @lem5356049)). Qed.
Lemma lem5356052 : term381 = True.
Proof. exact (EQ_MP (@lem5356051) (@lem5356049)). Qed.
Lemma lem5356053 : term380 = True.
Proof. exact (TRANS (@lem5356048) (@lem5356052)). Qed.
Lemma lem5356054 : True = term380.
Proof. exact (SYM (@lem5356053)). Qed.
Lemma lem5356055 : term380.
Proof. exact (EQ_MP (@lem5356054) (@lem0)). Qed.
Lemma lem5356056 : term585.
Proof. exact (@lem5356045 (@lem5356055)). Qed.
Lemma lem5356058 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356059 : term380 = term381.
Proof. exact (@lem5356058 (NUMERAL 0) term146). Qed.
Lemma lem5356060 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356061 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356062 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356061 h1) (fun h1 : term381 = True => @lem5356060)). Qed.
Lemma lem5356063 : term381 = True.
Proof. exact (EQ_MP (@lem5356062) (@lem5356060)). Qed.
Lemma lem5356064 : term380 = True.
Proof. exact (TRANS (@lem5356059) (@lem5356063)). Qed.
Lemma lem5356065 : True = term380.
Proof. exact (SYM (@lem5356064)). Qed.
Lemma lem5356066 : term380.
Proof. exact (EQ_MP (@lem5356065) (@lem0)). Qed.
Lemma lem5356067 : term583 = term586.
Proof. exact (@lem5356056 (@lem5356066)). Qed.
Lemma lem5356069 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356070 : term321 = term322.
Proof. exact (@lem5356069 term146 term146). Qed.
Lemma lem5356071 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356072 : term324 = term146.
Proof. exact (EQ_MP (@lem5356071) (@lem940073)). Qed.
Lemma lem5356073 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356074 : term322 = term267.
Proof. exact (MK_COMB (@lem5356073) (@lem5356072)). Qed.
Lemma lem5356075 : term321 = term267.
Proof. exact (TRANS (@lem5356070) (@lem5356074)). Qed.
Lemma lem5356077 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356078 : term392 = term254.
Proof. exact (@lem5356077 term146). Qed.
Lemma lem5356079 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5356080 : term587 = term581.
Proof. exact (MK_COMB (@lem5356079) (@lem5356078)). Qed.
Lemma lem5356081 : term586 = term380.
Proof. exact (MK_COMB (@lem5356080) (@lem5356075)). Qed.
Lemma lem5356083 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356084 : term380 = term381.
Proof. exact (@lem5356083 (NUMERAL 0) term146). Qed.
Lemma lem5356085 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356086 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356087 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356086 h1) (fun h1 : term381 = True => @lem5356085)). Qed.
Lemma lem5356088 : term381 = True.
Proof. exact (EQ_MP (@lem5356087) (@lem5356085)). Qed.
Lemma lem5356089 : term380 = True.
Proof. exact (TRANS (@lem5356084) (@lem5356088)). Qed.
Lemma lem5356090 : term586 = True.
Proof. exact (TRANS (@lem5356081) (@lem5356089)). Qed.
Lemma lem5356091 : term583 = True.
Proof. exact (TRANS (@lem5356067) (@lem5356090)). Qed.
Lemma lem5356092 : term380 = True.
Proof. exact (TRANS (@lem5356044) (@lem5356091)). Qed.
Lemma lem5356093 : term580 = True.
Proof. exact (TRANS (@lem5356035) (@lem5356092)). Qed.
Lemma lem5356094 : True = term580.
Proof. exact (SYM (@lem5356093)). Qed.
Lemma lem5356095 : term580.
Proof. exact (EQ_MP (@lem5356094) (@lem0)). Qed.
Lemma lem5356096 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term588 _69724 _69726.
Proof. exact (conj (@lem5356095) (@lem5356029 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356098 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5356099 (_69724 : int) (_69726 : int) : term590 _69724 _69726.
Proof. exact (@lem5356098 term267 (term357 _69724 _69726)). Qed.
Lemma lem5356100 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term591 _69724 _69726.
Proof. exact (@lem5356099 _69724 _69726 (@lem5356096 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356101 (_69724 : int) (_69726 : int) : (term592 _69724 _69726) = (term357 _69724 _69726).
Proof. exact (@lem1982733 (term357 _69724 _69726)). Qed.
Lemma lem5356102 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5356103 (_69724 : int) (_69726 : int) : (term593 _69724 _69726) = (term359 _69724 _69726).
Proof. exact (MK_COMB (@lem5356102) (@lem5356101 _69724 _69726)). Qed.
Lemma lem5356104 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5356105 (_69724 : int) (_69726 : int) : (term591 _69724 _69726) = (term360 _69724 _69726).
Proof. exact (MK_COMB (@lem5356103 _69724 _69726) (@lem5356104)). Qed.
Lemma lem5356106 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term360 _69724 _69726.
Proof. exact (EQ_MP (@lem5356105 _69724 _69726) (@lem5356100 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356108 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5356109 : term580 = term380.
Proof. exact (@lem5356108 term254 term267). Qed.
Lemma lem5356111 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356112 : term267 = term346.
Proof. exact (@lem5356111 term146). Qed.
Lemma lem5356114 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356115 : term254 = term309.
Proof. exact (@lem5356114 (NUMERAL 0)). Qed.
Lemma lem5356116 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5356117 : term581 = term582.
Proof. exact (MK_COMB (@lem5356116) (@lem5356115)). Qed.
Lemma lem5356118 : term380 = term583.
Proof. exact (MK_COMB (@lem5356117) (@lem5356112)). Qed.
Lemma lem5356119 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5356121 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356122 : term380 = term381.
Proof. exact (@lem5356121 (NUMERAL 0) term146). Qed.
Lemma lem5356123 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356124 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356125 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356124 h1) (fun h1 : term381 = True => @lem5356123)). Qed.
Lemma lem5356126 : term381 = True.
Proof. exact (EQ_MP (@lem5356125) (@lem5356123)). Qed.
Lemma lem5356127 : term380 = True.
Proof. exact (TRANS (@lem5356122) (@lem5356126)). Qed.
Lemma lem5356128 : True = term380.
Proof. exact (SYM (@lem5356127)). Qed.
Lemma lem5356129 : term380.
Proof. exact (EQ_MP (@lem5356128) (@lem0)). Qed.
Lemma lem5356130 : term585.
Proof. exact (@lem5356119 (@lem5356129)). Qed.
Lemma lem5356132 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356133 : term380 = term381.
Proof. exact (@lem5356132 (NUMERAL 0) term146). Qed.
Lemma lem5356134 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356135 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356136 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356135 h1) (fun h1 : term381 = True => @lem5356134)). Qed.
Lemma lem5356137 : term381 = True.
Proof. exact (EQ_MP (@lem5356136) (@lem5356134)). Qed.
Lemma lem5356138 : term380 = True.
Proof. exact (TRANS (@lem5356133) (@lem5356137)). Qed.
Lemma lem5356139 : True = term380.
Proof. exact (SYM (@lem5356138)). Qed.
Lemma lem5356140 : term380.
Proof. exact (EQ_MP (@lem5356139) (@lem0)). Qed.
Lemma lem5356141 : term583 = term586.
Proof. exact (@lem5356130 (@lem5356140)). Qed.
Lemma lem5356143 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356144 : term321 = term322.
Proof. exact (@lem5356143 term146 term146). Qed.
Lemma lem5356145 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356146 : term324 = term146.
Proof. exact (EQ_MP (@lem5356145) (@lem940073)). Qed.
Lemma lem5356147 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356148 : term322 = term267.
Proof. exact (MK_COMB (@lem5356147) (@lem5356146)). Qed.
Lemma lem5356149 : term321 = term267.
Proof. exact (TRANS (@lem5356144) (@lem5356148)). Qed.
Lemma lem5356151 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356152 : term392 = term254.
Proof. exact (@lem5356151 term146). Qed.
Lemma lem5356153 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5356154 : term587 = term581.
Proof. exact (MK_COMB (@lem5356153) (@lem5356152)). Qed.
Lemma lem5356155 : term586 = term380.
Proof. exact (MK_COMB (@lem5356154) (@lem5356149)). Qed.
Lemma lem5356157 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356158 : term380 = term381.
Proof. exact (@lem5356157 (NUMERAL 0) term146). Qed.
Lemma lem5356159 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356160 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356161 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356160 h1) (fun h1 : term381 = True => @lem5356159)). Qed.
Lemma lem5356162 : term381 = True.
Proof. exact (EQ_MP (@lem5356161) (@lem5356159)). Qed.
Lemma lem5356163 : term380 = True.
Proof. exact (TRANS (@lem5356158) (@lem5356162)). Qed.
Lemma lem5356164 : term586 = True.
Proof. exact (TRANS (@lem5356155) (@lem5356163)). Qed.
Lemma lem5356165 : term583 = True.
Proof. exact (TRANS (@lem5356141) (@lem5356164)). Qed.
Lemma lem5356166 : term380 = True.
Proof. exact (TRANS (@lem5356118) (@lem5356165)). Qed.
Lemma lem5356167 : term580 = True.
Proof. exact (TRANS (@lem5356109) (@lem5356166)). Qed.
Lemma lem5356168 : True = term580.
Proof. exact (SYM (@lem5356167)). Qed.
Lemma lem5356169 : term580.
Proof. exact (EQ_MP (@lem5356168) (@lem0)). Qed.
Lemma lem5356170 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term644 _69724 _69726.
Proof. exact (conj (@lem5356169) (@lem5356032 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356172 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5356173 (_69724 : int) (_69726 : int) : term645 _69724 _69726.
Proof. exact (@lem5356172 term267 (term361 _69724 _69726)). Qed.
Lemma lem5356174 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term646 _69724 _69726.
Proof. exact (@lem5356173 _69724 _69726 (@lem5356170 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356175 (_69724 : int) (_69726 : int) : (term647 _69724 _69726) = (term361 _69724 _69726).
Proof. exact (@lem1982733 (term361 _69724 _69726)). Qed.
Lemma lem5356176 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5356177 (_69724 : int) (_69726 : int) : (term648 _69724 _69726) = (term362 _69724 _69726).
Proof. exact (MK_COMB (@lem5356176) (@lem5356175 _69724 _69726)). Qed.
Lemma lem5356178 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5356179 (_69724 : int) (_69726 : int) : (term646 _69724 _69726) = (term363 _69724 _69726).
Proof. exact (MK_COMB (@lem5356177 _69724 _69726) (@lem5356178)). Qed.
Lemma lem5356180 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term363 _69724 _69726.
Proof. exact (EQ_MP (@lem5356179 _69724 _69726) (@lem5356174 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356181 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term680 _69724 _69726.
Proof. exact (conj (@lem5356180 _69725 _69724 _69726 h1) (@lem5356106 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356183 (x : real) (y : real) : term600 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5356184 (_69724 : int) (_69726 : int) : term681 _69724 _69726.
Proof. exact (@lem5356183 (term361 _69724 _69726) (term357 _69724 _69726)). Qed.
Lemma lem5356185 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term682 _69724 _69726.
Proof. exact (@lem5356184 _69724 _69726 (@lem5356181 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356186 (_69724 : int) (_69726 : int) : (term683 _69724 _69726) = (term684 _69724 _69726).
Proof. exact (@lem1982753 (term337 _69724) (real_of_int _69724) (term659 _69726) (term356 _69726)). Qed.
Lemma lem5356187 (_69724 : int) : (term605 _69724) = (term606 _69724).
Proof. exact (@lem1982713 term312 (real_of_int _69724)). Qed.
Lemma lem5356189 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356190 : term267 = term346.
Proof. exact (@lem5356189 term146). Qed.
Lemma lem5356192 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5356193 : term312 = term313.
Proof. exact (@lem5356192 term146). Qed.
Lemma lem5356194 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356195 : term607 = term608.
Proof. exact (MK_COMB (@lem5356194) (@lem5356193)). Qed.
Lemma lem5356196 : term609 = term610.
Proof. exact (MK_COMB (@lem5356195) (@lem5356190)). Qed.
Lemma lem5356197 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5356199 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356200 : term380 = term381.
Proof. exact (@lem5356199 (NUMERAL 0) term146). Qed.
Lemma lem5356201 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356202 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356203 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356202 h1) (fun h1 : term381 = True => @lem5356201)). Qed.
Lemma lem5356204 : term381 = True.
Proof. exact (EQ_MP (@lem5356203) (@lem5356201)). Qed.
Lemma lem5356205 : term380 = True.
Proof. exact (TRANS (@lem5356200) (@lem5356204)). Qed.
Lemma lem5356206 : True = term380.
Proof. exact (SYM (@lem5356205)). Qed.
Lemma lem5356207 : term380.
Proof. exact (EQ_MP (@lem5356206) (@lem0)). Qed.
Lemma lem5356208 : term612.
Proof. exact (@lem5356197 (@lem5356207)). Qed.
Lemma lem5356210 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356211 : term380 = term381.
Proof. exact (@lem5356210 (NUMERAL 0) term146). Qed.
Lemma lem5356212 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356213 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356214 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356213 h1) (fun h1 : term381 = True => @lem5356212)). Qed.
Lemma lem5356215 : term381 = True.
Proof. exact (EQ_MP (@lem5356214) (@lem5356212)). Qed.
Lemma lem5356216 : term380 = True.
Proof. exact (TRANS (@lem5356211) (@lem5356215)). Qed.
Lemma lem5356217 : True = term380.
Proof. exact (SYM (@lem5356216)). Qed.
Lemma lem5356218 : term380.
Proof. exact (EQ_MP (@lem5356217) (@lem0)). Qed.
Lemma lem5356219 : term613.
Proof. exact (@lem5356208 (@lem5356218)). Qed.
Lemma lem5356221 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356222 : term380 = term381.
Proof. exact (@lem5356221 (NUMERAL 0) term146). Qed.
Lemma lem5356223 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356224 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356225 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356224 h1) (fun h1 : term381 = True => @lem5356223)). Qed.
Lemma lem5356226 : term381 = True.
Proof. exact (EQ_MP (@lem5356225) (@lem5356223)). Qed.
Lemma lem5356227 : term380 = True.
Proof. exact (TRANS (@lem5356222) (@lem5356226)). Qed.
Lemma lem5356228 : True = term380.
Proof. exact (SYM (@lem5356227)). Qed.
Lemma lem5356229 : term380.
Proof. exact (EQ_MP (@lem5356228) (@lem0)). Qed.
Lemma lem5356230 : term614.
Proof. exact (@lem5356219 (@lem5356229)). Qed.
Lemma lem5356232 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356233 : term321 = term322.
Proof. exact (@lem5356232 term146 term146). Qed.
Lemma lem5356234 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356235 : term324 = term146.
Proof. exact (EQ_MP (@lem5356234) (@lem940073)). Qed.
Lemma lem5356236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356237 : term322 = term267.
Proof. exact (MK_COMB (@lem5356236) (@lem5356235)). Qed.
Lemma lem5356238 : term321 = term267.
Proof. exact (TRANS (@lem5356233) (@lem5356237)). Qed.
Lemma lem5356240 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5356241 : term347 = term352.
Proof. exact (@lem5356240 term146 term146). Qed.
Lemma lem5356242 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356243 : term324 = term146.
Proof. exact (EQ_MP (@lem5356242) (@lem940073)). Qed.
Lemma lem5356244 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356245 : term322 = term267.
Proof. exact (MK_COMB (@lem5356244) (@lem5356243)). Qed.
Lemma lem5356246 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5356247 : term352 = term312.
Proof. exact (MK_COMB (@lem5356246) (@lem5356245)). Qed.
Lemma lem5356248 : term347 = term312.
Proof. exact (TRANS (@lem5356241) (@lem5356247)). Qed.
Lemma lem5356249 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356250 : term615 = term607.
Proof. exact (MK_COMB (@lem5356249) (@lem5356248)). Qed.
Lemma lem5356251 : term616 = term609.
Proof. exact (MK_COMB (@lem5356250) (@lem5356238)). Qed.
Lemma lem5356253 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5356254 : term609 = term254.
Proof. exact (@lem5356253 term146). Qed.
Lemma lem5356255 : term616 = term254.
Proof. exact (TRANS (@lem5356251) (@lem5356254)). Qed.
Lemma lem5356256 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5356257 : term618 = term390.
Proof. exact (MK_COMB (@lem5356256) (@lem5356255)). Qed.
Lemma lem5356258 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5356259 : term619 = term392.
Proof. exact (MK_COMB (@lem5356257) (@lem5356258)). Qed.
Lemma lem5356261 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356262 : term392 = term254.
Proof. exact (@lem5356261 term146). Qed.
Lemma lem5356263 : term619 = term254.
Proof. exact (TRANS (@lem5356259) (@lem5356262)). Qed.
Lemma lem5356265 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356266 : term321 = term322.
Proof. exact (@lem5356265 term146 term146). Qed.
Lemma lem5356267 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356268 : term324 = term146.
Proof. exact (EQ_MP (@lem5356267) (@lem940073)). Qed.
Lemma lem5356269 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356270 : term322 = term267.
Proof. exact (MK_COMB (@lem5356269) (@lem5356268)). Qed.
Lemma lem5356271 : term321 = term267.
Proof. exact (TRANS (@lem5356266) (@lem5356270)). Qed.
Lemma lem5356272 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5356273 : term394 = term392.
Proof. exact (MK_COMB (@lem5356272) (@lem5356271)). Qed.
Lemma lem5356275 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356276 : term392 = term254.
Proof. exact (@lem5356275 term146). Qed.
Lemma lem5356277 : term394 = term254.
Proof. exact (TRANS (@lem5356273) (@lem5356276)). Qed.
Lemma lem5356278 : term254 = term394.
Proof. exact (SYM (@lem5356277)). Qed.
Lemma lem5356279 : term619 = term394.
Proof. exact (TRANS (@lem5356263) (@lem5356278)). Qed.
Lemma lem5356280 : term610 = term309.
Proof. exact (@lem5356230 (@lem5356279)). Qed.
Lemma lem5356281 : term609 = term309.
Proof. exact (TRANS (@lem5356196) (@lem5356280)). Qed.
Lemma lem5356283 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5356284 : term309 = term254.
Proof. exact (@lem5356283 term254). Qed.
Lemma lem5356285 : term609 = term254.
Proof. exact (TRANS (@lem5356281) (@lem5356284)). Qed.
Lemma lem5356286 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5356287 : term620 = term390.
Proof. exact (MK_COMB (@lem5356286) (@lem5356285)). Qed.
Lemma lem5356288 (_69724 : int) : (real_of_int _69724) = (real_of_int _69724).
Proof. exact (eq_refl (real_of_int _69724)). Qed.
Lemma lem5356289 (_69724 : int) : (term606 _69724) = (term621 _69724).
Proof. exact (MK_COMB (@lem5356287) (@lem5356288 _69724)). Qed.
Lemma lem5356290 (_69724 : int) : (term605 _69724) = (term621 _69724).
Proof. exact (TRANS (@lem5356187 _69724) (@lem5356289 _69724)). Qed.
Lemma lem5356291 (_69724 : int) : (term621 _69724) = term254.
Proof. exact (@lem1982719 (real_of_int _69724)). Qed.
Lemma lem5356292 (_69724 : int) : (term605 _69724) = term254.
Proof. exact (TRANS (@lem5356290 _69724) (@lem5356291 _69724)). Qed.
Lemma lem5356293 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356294 (_69724 : int) : (term622 _69724) = term623.
Proof. exact (MK_COMB (@lem5356293) (@lem5356292 _69724)). Qed.
Lemma lem5356295 (_69726 : int) : (term685 _69726) = (term686 _69726).
Proof. exact (@lem1982753 (real_of_int _69726) (term337 _69726) term312 term312). Qed.
Lemma lem5356296 (_69726 : int) : (term626 _69726) = (term606 _69726).
Proof. exact (@lem1982715 term312 (real_of_int _69726)). Qed.
Lemma lem5356298 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356299 : term267 = term346.
Proof. exact (@lem5356298 term146). Qed.
Lemma lem5356301 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5356302 : term312 = term313.
Proof. exact (@lem5356301 term146). Qed.
Lemma lem5356303 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356304 : term607 = term608.
Proof. exact (MK_COMB (@lem5356303) (@lem5356302)). Qed.
Lemma lem5356305 : term609 = term610.
Proof. exact (MK_COMB (@lem5356304) (@lem5356299)). Qed.
Lemma lem5356306 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5356308 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356309 : term380 = term381.
Proof. exact (@lem5356308 (NUMERAL 0) term146). Qed.
Lemma lem5356310 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356311 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356312 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356311 h1) (fun h1 : term381 = True => @lem5356310)). Qed.
Lemma lem5356313 : term381 = True.
Proof. exact (EQ_MP (@lem5356312) (@lem5356310)). Qed.
Lemma lem5356314 : term380 = True.
Proof. exact (TRANS (@lem5356309) (@lem5356313)). Qed.
Lemma lem5356315 : True = term380.
Proof. exact (SYM (@lem5356314)). Qed.
Lemma lem5356316 : term380.
Proof. exact (EQ_MP (@lem5356315) (@lem0)). Qed.
Lemma lem5356317 : term612.
Proof. exact (@lem5356306 (@lem5356316)). Qed.
Lemma lem5356319 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356320 : term380 = term381.
Proof. exact (@lem5356319 (NUMERAL 0) term146). Qed.
Lemma lem5356321 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356322 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356323 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356322 h1) (fun h1 : term381 = True => @lem5356321)). Qed.
Lemma lem5356324 : term381 = True.
Proof. exact (EQ_MP (@lem5356323) (@lem5356321)). Qed.
Lemma lem5356325 : term380 = True.
Proof. exact (TRANS (@lem5356320) (@lem5356324)). Qed.
Lemma lem5356326 : True = term380.
Proof. exact (SYM (@lem5356325)). Qed.
Lemma lem5356327 : term380.
Proof. exact (EQ_MP (@lem5356326) (@lem0)). Qed.
Lemma lem5356328 : term613.
Proof. exact (@lem5356317 (@lem5356327)). Qed.
Lemma lem5356330 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356331 : term380 = term381.
Proof. exact (@lem5356330 (NUMERAL 0) term146). Qed.
Lemma lem5356332 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356333 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356334 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356333 h1) (fun h1 : term381 = True => @lem5356332)). Qed.
Lemma lem5356335 : term381 = True.
Proof. exact (EQ_MP (@lem5356334) (@lem5356332)). Qed.
Lemma lem5356336 : term380 = True.
Proof. exact (TRANS (@lem5356331) (@lem5356335)). Qed.
Lemma lem5356337 : True = term380.
Proof. exact (SYM (@lem5356336)). Qed.
Lemma lem5356338 : term380.
Proof. exact (EQ_MP (@lem5356337) (@lem0)). Qed.
Lemma lem5356339 : term614.
Proof. exact (@lem5356328 (@lem5356338)). Qed.
Lemma lem5356341 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356342 : term321 = term322.
Proof. exact (@lem5356341 term146 term146). Qed.
Lemma lem5356343 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356344 : term324 = term146.
Proof. exact (EQ_MP (@lem5356343) (@lem940073)). Qed.
Lemma lem5356345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356346 : term322 = term267.
Proof. exact (MK_COMB (@lem5356345) (@lem5356344)). Qed.
Lemma lem5356347 : term321 = term267.
Proof. exact (TRANS (@lem5356342) (@lem5356346)). Qed.
Lemma lem5356349 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5356350 : term347 = term352.
Proof. exact (@lem5356349 term146 term146). Qed.
Lemma lem5356351 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356352 : term324 = term146.
Proof. exact (EQ_MP (@lem5356351) (@lem940073)). Qed.
Lemma lem5356353 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356354 : term322 = term267.
Proof. exact (MK_COMB (@lem5356353) (@lem5356352)). Qed.
Lemma lem5356355 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5356356 : term352 = term312.
Proof. exact (MK_COMB (@lem5356355) (@lem5356354)). Qed.
Lemma lem5356357 : term347 = term312.
Proof. exact (TRANS (@lem5356350) (@lem5356356)). Qed.
Lemma lem5356358 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356359 : term615 = term607.
Proof. exact (MK_COMB (@lem5356358) (@lem5356357)). Qed.
Lemma lem5356360 : term616 = term609.
Proof. exact (MK_COMB (@lem5356359) (@lem5356347)). Qed.
Lemma lem5356362 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5356363 : term609 = term254.
Proof. exact (@lem5356362 term146). Qed.
Lemma lem5356364 : term616 = term254.
Proof. exact (TRANS (@lem5356360) (@lem5356363)). Qed.
Lemma lem5356365 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5356366 : term618 = term390.
Proof. exact (MK_COMB (@lem5356365) (@lem5356364)). Qed.
Lemma lem5356367 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5356368 : term619 = term392.
Proof. exact (MK_COMB (@lem5356366) (@lem5356367)). Qed.
Lemma lem5356370 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356371 : term392 = term254.
Proof. exact (@lem5356370 term146). Qed.
Lemma lem5356372 : term619 = term254.
Proof. exact (TRANS (@lem5356368) (@lem5356371)). Qed.
Lemma lem5356374 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356375 : term321 = term322.
Proof. exact (@lem5356374 term146 term146). Qed.
Lemma lem5356376 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356377 : term324 = term146.
Proof. exact (EQ_MP (@lem5356376) (@lem940073)). Qed.
Lemma lem5356378 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356379 : term322 = term267.
Proof. exact (MK_COMB (@lem5356378) (@lem5356377)). Qed.
Lemma lem5356380 : term321 = term267.
Proof. exact (TRANS (@lem5356375) (@lem5356379)). Qed.
Lemma lem5356381 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5356382 : term394 = term392.
Proof. exact (MK_COMB (@lem5356381) (@lem5356380)). Qed.
Lemma lem5356384 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356385 : term392 = term254.
Proof. exact (@lem5356384 term146). Qed.
Lemma lem5356386 : term394 = term254.
Proof. exact (TRANS (@lem5356382) (@lem5356385)). Qed.
Lemma lem5356387 : term254 = term394.
Proof. exact (SYM (@lem5356386)). Qed.
Lemma lem5356388 : term619 = term394.
Proof. exact (TRANS (@lem5356372) (@lem5356387)). Qed.
Lemma lem5356389 : term610 = term309.
Proof. exact (@lem5356339 (@lem5356388)). Qed.
Lemma lem5356390 : term609 = term309.
Proof. exact (TRANS (@lem5356305) (@lem5356389)). Qed.
Lemma lem5356392 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5356393 : term309 = term254.
Proof. exact (@lem5356392 term254). Qed.
Lemma lem5356394 : term609 = term254.
Proof. exact (TRANS (@lem5356390) (@lem5356393)). Qed.
Lemma lem5356395 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5356396 : term620 = term390.
Proof. exact (MK_COMB (@lem5356395) (@lem5356394)). Qed.
Lemma lem5356397 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5356398 (_69726 : int) : (term606 _69726) = (term621 _69726).
Proof. exact (MK_COMB (@lem5356396) (@lem5356397 _69726)). Qed.
Lemma lem5356399 (_69726 : int) : (term626 _69726) = (term621 _69726).
Proof. exact (TRANS (@lem5356296 _69726) (@lem5356398 _69726)). Qed.
Lemma lem5356400 (_69726 : int) : (term621 _69726) = term254.
Proof. exact (@lem1982719 (real_of_int _69726)). Qed.
Lemma lem5356401 (_69726 : int) : (term626 _69726) = term254.
Proof. exact (TRANS (@lem5356399 _69726) (@lem5356400 _69726)). Qed.
Lemma lem5356402 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356403 (_69726 : int) : (term627 _69726) = term623.
Proof. exact (MK_COMB (@lem5356402) (@lem5356401 _69726)). Qed.
Lemma lem5356405 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5356406 : term312 = term313.
Proof. exact (@lem5356405 term146). Qed.
Lemma lem5356408 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5356409 : term312 = term313.
Proof. exact (@lem5356408 term146). Qed.
Lemma lem5356410 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356411 : term607 = term608.
Proof. exact (MK_COMB (@lem5356410) (@lem5356409)). Qed.
Lemma lem5356412 : term687 = term688.
Proof. exact (MK_COMB (@lem5356411) (@lem5356406)). Qed.
Lemma lem5356413 : term689.
Proof. exact (@lem1981473 term312 term267 term312 term267 term690 term267). Qed.
Lemma lem5356415 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356416 : term380 = term381.
Proof. exact (@lem5356415 (NUMERAL 0) term146). Qed.
Lemma lem5356417 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356418 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356419 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356418 h1) (fun h1 : term381 = True => @lem5356417)). Qed.
Lemma lem5356420 : term381 = True.
Proof. exact (EQ_MP (@lem5356419) (@lem5356417)). Qed.
Lemma lem5356421 : term380 = True.
Proof. exact (TRANS (@lem5356416) (@lem5356420)). Qed.
Lemma lem5356422 : True = term380.
Proof. exact (SYM (@lem5356421)). Qed.
Lemma lem5356423 : term380.
Proof. exact (EQ_MP (@lem5356422) (@lem0)). Qed.
Lemma lem5356424 : term691.
Proof. exact (@lem5356413 (@lem5356423)). Qed.
Lemma lem5356426 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356427 : term380 = term381.
Proof. exact (@lem5356426 (NUMERAL 0) term146). Qed.
Lemma lem5356428 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356429 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356430 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356429 h1) (fun h1 : term381 = True => @lem5356428)). Qed.
Lemma lem5356431 : term381 = True.
Proof. exact (EQ_MP (@lem5356430) (@lem5356428)). Qed.
Lemma lem5356432 : term380 = True.
Proof. exact (TRANS (@lem5356427) (@lem5356431)). Qed.
Lemma lem5356433 : True = term380.
Proof. exact (SYM (@lem5356432)). Qed.
Lemma lem5356434 : term380.
Proof. exact (EQ_MP (@lem5356433) (@lem0)). Qed.
Lemma lem5356435 : term692.
Proof. exact (@lem5356424 (@lem5356434)). Qed.
Lemma lem5356437 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356438 : term380 = term381.
Proof. exact (@lem5356437 (NUMERAL 0) term146). Qed.
Lemma lem5356439 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356440 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356441 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356440 h1) (fun h1 : term381 = True => @lem5356439)). Qed.
Lemma lem5356442 : term381 = True.
Proof. exact (EQ_MP (@lem5356441) (@lem5356439)). Qed.
Lemma lem5356443 : term380 = True.
Proof. exact (TRANS (@lem5356438) (@lem5356442)). Qed.
Lemma lem5356444 : True = term380.
Proof. exact (SYM (@lem5356443)). Qed.
Lemma lem5356445 : term380.
Proof. exact (EQ_MP (@lem5356444) (@lem0)). Qed.
Lemma lem5356446 : term693.
Proof. exact (@lem5356435 (@lem5356445)). Qed.
Lemma lem5356448 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5356449 : term347 = term352.
Proof. exact (@lem5356448 term146 term146). Qed.
Lemma lem5356450 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356451 : term324 = term146.
Proof. exact (EQ_MP (@lem5356450) (@lem940073)). Qed.
Lemma lem5356452 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356453 : term322 = term267.
Proof. exact (MK_COMB (@lem5356452) (@lem5356451)). Qed.
Lemma lem5356454 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5356455 : term352 = term312.
Proof. exact (MK_COMB (@lem5356454) (@lem5356453)). Qed.
Lemma lem5356456 : term347 = term312.
Proof. exact (TRANS (@lem5356449) (@lem5356455)). Qed.
Lemma lem5356458 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5356459 : term347 = term352.
Proof. exact (@lem5356458 term146 term146). Qed.
Lemma lem5356460 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356461 : term324 = term146.
Proof. exact (EQ_MP (@lem5356460) (@lem940073)). Qed.
Lemma lem5356462 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356463 : term322 = term267.
Proof. exact (MK_COMB (@lem5356462) (@lem5356461)). Qed.
Lemma lem5356464 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5356465 : term352 = term312.
Proof. exact (MK_COMB (@lem5356464) (@lem5356463)). Qed.
Lemma lem5356466 : term347 = term312.
Proof. exact (TRANS (@lem5356459) (@lem5356465)). Qed.
Lemma lem5356467 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356468 : term615 = term607.
Proof. exact (MK_COMB (@lem5356467) (@lem5356466)). Qed.
Lemma lem5356469 : term694 = term687.
Proof. exact (MK_COMB (@lem5356468) (@lem5356456)). Qed.
Lemma lem5356470 : term687 = term695.
Proof. exact (@lem1367763 term146 term146). Qed.
Lemma lem5356471 : term696 = term697.
Proof. exact (@lem706885). Qed.
Lemma lem5356472 : (term696 = term697) = (term698 = term699).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term697). Qed.
Lemma lem5356473 : term698 = term699.
Proof. exact (EQ_MP (@lem5356472) (@lem5356471)). Qed.
Lemma lem5356474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356475 : term700 = term701.
Proof. exact (MK_COMB (@lem5356474) (@lem5356473)). Qed.
Lemma lem5356476 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5356477 : term695 = term690.
Proof. exact (MK_COMB (@lem5356476) (@lem5356475)). Qed.
Lemma lem5356478 : term687 = term690.
Proof. exact (TRANS (@lem5356470) (@lem5356477)). Qed.
Lemma lem5356479 : term694 = term690.
Proof. exact (TRANS (@lem5356469) (@lem5356478)). Qed.
Lemma lem5356480 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5356481 : term702 = term703.
Proof. exact (MK_COMB (@lem5356480) (@lem5356479)). Qed.
Lemma lem5356482 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5356483 : term704 = term705.
Proof. exact (MK_COMB (@lem5356481) (@lem5356482)). Qed.
Lemma lem5356485 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5356486 : term705 = term706.
Proof. exact (@lem5356485 term699 term146). Qed.
Lemma lem5356487 : term707 = term697.
Proof. exact (@lem996237 term697). Qed.
Lemma lem5356488 : (term707 = term697) = (term708 = term699).
Proof. exact (@lem1007663 term697 (BIT1 0) term697). Qed.
Lemma lem5356489 : term708 = term699.
Proof. exact (EQ_MP (@lem5356488) (@lem5356487)). Qed.
Lemma lem5356490 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356491 : term709 = term701.
Proof. exact (MK_COMB (@lem5356490) (@lem5356489)). Qed.
Lemma lem5356492 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5356493 : term706 = term690.
Proof. exact (MK_COMB (@lem5356492) (@lem5356491)). Qed.
Lemma lem5356494 : term705 = term690.
Proof. exact (TRANS (@lem5356486) (@lem5356493)). Qed.
Lemma lem5356495 : term704 = term690.
Proof. exact (TRANS (@lem5356483) (@lem5356494)). Qed.
Lemma lem5356497 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356498 : term321 = term322.
Proof. exact (@lem5356497 term146 term146). Qed.
Lemma lem5356499 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356500 : term324 = term146.
Proof. exact (EQ_MP (@lem5356499) (@lem940073)). Qed.
Lemma lem5356501 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356502 : term322 = term267.
Proof. exact (MK_COMB (@lem5356501) (@lem5356500)). Qed.
Lemma lem5356503 : term321 = term267.
Proof. exact (TRANS (@lem5356498) (@lem5356502)). Qed.
Lemma lem5356504 : term703 = term703.
Proof. exact (eq_refl term703). Qed.
Lemma lem5356505 : term710 = term705.
Proof. exact (MK_COMB (@lem5356504) (@lem5356503)). Qed.
Lemma lem5356507 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5356508 : term705 = term706.
Proof. exact (@lem5356507 term699 term146). Qed.
Lemma lem5356509 : term707 = term697.
Proof. exact (@lem996237 term697). Qed.
Lemma lem5356510 : (term707 = term697) = (term708 = term699).
Proof. exact (@lem1007663 term697 (BIT1 0) term697). Qed.
Lemma lem5356511 : term708 = term699.
Proof. exact (EQ_MP (@lem5356510) (@lem5356509)). Qed.
Lemma lem5356512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356513 : term709 = term701.
Proof. exact (MK_COMB (@lem5356512) (@lem5356511)). Qed.
Lemma lem5356514 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5356515 : term706 = term690.
Proof. exact (MK_COMB (@lem5356514) (@lem5356513)). Qed.
Lemma lem5356516 : term705 = term690.
Proof. exact (TRANS (@lem5356508) (@lem5356515)). Qed.
Lemma lem5356517 : term710 = term690.
Proof. exact (TRANS (@lem5356505) (@lem5356516)). Qed.
Lemma lem5356518 : term690 = term710.
Proof. exact (SYM (@lem5356517)). Qed.
Lemma lem5356519 : term704 = term710.
Proof. exact (TRANS (@lem5356495) (@lem5356518)). Qed.
Lemma lem5356520 : term688 = term711.
Proof. exact (@lem5356446 (@lem5356519)). Qed.
Lemma lem5356521 : term687 = term711.
Proof. exact (TRANS (@lem5356412) (@lem5356520)). Qed.
Lemma lem5356523 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5356524 : term711 = term690.
Proof. exact (@lem5356523 term690). Qed.
Lemma lem5356525 : term687 = term690.
Proof. exact (TRANS (@lem5356521) (@lem5356524)). Qed.
Lemma lem5356526 (_69726 : int) : (term686 _69726) = term712.
Proof. exact (MK_COMB (@lem5356403 _69726) (@lem5356525)). Qed.
Lemma lem5356527 (_69726 : int) : (term685 _69726) = term712.
Proof. exact (TRANS (@lem5356295 _69726) (@lem5356526 _69726)). Qed.
Lemma lem5356528 : term712 = term690.
Proof. exact (@lem1982721 term690). Qed.
Lemma lem5356529 (_69726 : int) : (term685 _69726) = term690.
Proof. exact (TRANS (@lem5356527 _69726) (@lem5356528)). Qed.
Lemma lem5356530 (_69724 : int) (_69726 : int) : (term684 _69724 _69726) = term712.
Proof. exact (MK_COMB (@lem5356294 _69724) (@lem5356529 _69726)). Qed.
Lemma lem5356531 (_69724 : int) (_69726 : int) : (term683 _69724 _69726) = term712.
Proof. exact (TRANS (@lem5356186 _69724 _69726) (@lem5356530 _69724 _69726)). Qed.
Lemma lem5356532 : term712 = term690.
Proof. exact (@lem1982721 term690). Qed.
Lemma lem5356533 (_69724 : int) (_69726 : int) : (term683 _69724 _69726) = term690.
Proof. exact (TRANS (@lem5356531 _69724 _69726) (@lem5356532)). Qed.
Lemma lem5356534 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5356535 (_69724 : int) (_69726 : int) : (term713 _69724 _69726) = term714.
Proof. exact (MK_COMB (@lem5356534) (@lem5356533 _69724 _69726)). Qed.
Lemma lem5356536 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5356537 (_69724 : int) (_69726 : int) : (term682 _69724 _69726) = term715.
Proof. exact (MK_COMB (@lem5356535 _69724 _69726) (@lem5356536)). Qed.
Lemma lem5356538 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : term715.
Proof. exact (EQ_MP (@lem5356537 _69724 _69726) (@lem5356185 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356540 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5356541 : term715 = term716.
Proof. exact (@lem5356540 term254 term690). Qed.
Lemma lem5356543 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5356544 : term690 = term711.
Proof. exact (@lem5356543 term699). Qed.
Lemma lem5356546 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356547 : term254 = term309.
Proof. exact (@lem5356546 (NUMERAL 0)). Qed.
Lemma lem5356548 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5356549 : term256 = term633.
Proof. exact (MK_COMB (@lem5356548) (@lem5356547)). Qed.
Lemma lem5356550 : term716 = term717.
Proof. exact (MK_COMB (@lem5356549) (@lem5356544)). Qed.
Lemma lem5356551 : term718.
Proof. exact (@lem1980026 term254 term267 term690 term267). Qed.
Lemma lem5356553 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356554 : term380 = term381.
Proof. exact (@lem5356553 (NUMERAL 0) term146). Qed.
Lemma lem5356555 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356556 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356557 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356556 h1) (fun h1 : term381 = True => @lem5356555)). Qed.
Lemma lem5356558 : term381 = True.
Proof. exact (EQ_MP (@lem5356557) (@lem5356555)). Qed.
Lemma lem5356559 : term380 = True.
Proof. exact (TRANS (@lem5356554) (@lem5356558)). Qed.
Lemma lem5356560 : True = term380.
Proof. exact (SYM (@lem5356559)). Qed.
Lemma lem5356561 : term380.
Proof. exact (EQ_MP (@lem5356560) (@lem0)). Qed.
Lemma lem5356562 : term719.
Proof. exact (@lem5356551 (@lem5356561)). Qed.
Lemma lem5356564 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356565 : term380 = term381.
Proof. exact (@lem5356564 (NUMERAL 0) term146). Qed.
Lemma lem5356566 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356567 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356568 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356567 h1) (fun h1 : term381 = True => @lem5356566)). Qed.
Lemma lem5356569 : term381 = True.
Proof. exact (EQ_MP (@lem5356568) (@lem5356566)). Qed.
Lemma lem5356570 : term380 = True.
Proof. exact (TRANS (@lem5356565) (@lem5356569)). Qed.
Lemma lem5356571 : True = term380.
Proof. exact (SYM (@lem5356570)). Qed.
Lemma lem5356572 : term380.
Proof. exact (EQ_MP (@lem5356571) (@lem0)). Qed.
Lemma lem5356573 : term717 = term720.
Proof. exact (@lem5356562 (@lem5356572)). Qed.
Lemma lem5356575 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5356576 : term705 = term706.
Proof. exact (@lem5356575 term699 term146). Qed.
Lemma lem5356577 : term707 = term697.
Proof. exact (@lem996237 term697). Qed.
Lemma lem5356578 : (term707 = term697) = (term708 = term699).
Proof. exact (@lem1007663 term697 (BIT1 0) term697). Qed.
Lemma lem5356579 : term708 = term699.
Proof. exact (EQ_MP (@lem5356578) (@lem5356577)). Qed.
Lemma lem5356580 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356581 : term709 = term701.
Proof. exact (MK_COMB (@lem5356580) (@lem5356579)). Qed.
Lemma lem5356582 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5356583 : term706 = term690.
Proof. exact (MK_COMB (@lem5356582) (@lem5356581)). Qed.
Lemma lem5356584 : term705 = term690.
Proof. exact (TRANS (@lem5356576) (@lem5356583)). Qed.
Lemma lem5356586 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356587 : term392 = term254.
Proof. exact (@lem5356586 term146). Qed.
Lemma lem5356588 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5356589 : term638 = term256.
Proof. exact (MK_COMB (@lem5356588) (@lem5356587)). Qed.
Lemma lem5356590 : term720 = term716.
Proof. exact (MK_COMB (@lem5356589) (@lem5356584)). Qed.
Lemma lem5356592 (m : nat) (n : nat) : (term639 m n) = (term640 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5356593 : term716 = term721.
Proof. exact (@lem5356592 (NUMERAL 0) term699). Qed.
Lemma lem5356594 : term722 = term697.
Proof. exact (@lem912803). Qed.
Lemma lem5356595 (h1 : term722 = term697) : (term699 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term697 h1). Qed.
Lemma lem5356596 : (term722 = term697) = ((term699 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term722 = term697 => @lem5356595 h1) (fun h1 : (term699 = (NUMERAL 0)) = False => @lem5356594)). Qed.
Lemma lem5356597 : (term699 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5356596) (@lem5356594)). Qed.
Lemma lem5356598 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5356599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5356600 : term642 = (and True).
Proof. exact (MK_COMB (@lem5356599) (@lem5356598)). Qed.
Lemma lem5356601 : term721 = (True /\ False).
Proof. exact (MK_COMB (@lem5356600) (@lem5356597)). Qed.
Lemma lem5356603 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5356604 : term721 = False.
Proof. exact (TRANS (@lem5356601) (@lem5356603)). Qed.
Lemma lem5356605 : term716 = False.
Proof. exact (TRANS (@lem5356593) (@lem5356604)). Qed.
Lemma lem5356606 : term720 = False.
Proof. exact (TRANS (@lem5356590) (@lem5356605)). Qed.
Lemma lem5356607 : term717 = False.
Proof. exact (TRANS (@lem5356573) (@lem5356606)). Qed.
Lemma lem5356608 : term716 = False.
Proof. exact (TRANS (@lem5356550) (@lem5356607)). Qed.
Lemma lem5356609 : term715 = False.
Proof. exact (TRANS (@lem5356541) (@lem5356608)). Qed.
Lemma lem5356610 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term679 _69725 _69724 _69726) : False.
Proof. exact (EQ_MP (@lem5356609) (@lem5356538 _69725 _69724 _69726 h1)). Qed.
Lemma lem5356611 (_69725 : int) (_69724 : int) (_69726 : int) (h1 : term557 _69725 _69724 _69726) : False.
Proof. exact (or_elim (@lem5355613 _69725 _69724 _69726 h1) (fun h0 : term671 _69725 _69724 _69726 => @lem5356019 _69725 _69724 _69726 h0) (fun h0 : term679 _69725 _69724 _69726 => @lem5356610 _69725 _69724 _69726 h0)). Qed.
Lemma lem5356612 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term553 _69724 _69725 _69726) : term553 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5356613 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term723 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5356614 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term554 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5356613 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356616 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term523 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5356614 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356618 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term492 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5356616 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356620 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term461 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5356618 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356621 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term340 _69724 _69725.
Proof. exact (proj1 (@lem5356618 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356622 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term363 _69725 _69726.
Proof. exact (proj2 (@lem5356620 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356623 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : (term336 _69724 _69726) = term254.
Proof. exact (proj1 (@lem5356620 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356625 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5356626 : term580 = term380.
Proof. exact (@lem5356625 term254 term267). Qed.
Lemma lem5356628 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356629 : term267 = term346.
Proof. exact (@lem5356628 term146). Qed.
Lemma lem5356631 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356632 : term254 = term309.
Proof. exact (@lem5356631 (NUMERAL 0)). Qed.
Lemma lem5356633 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5356634 : term581 = term582.
Proof. exact (MK_COMB (@lem5356633) (@lem5356632)). Qed.
Lemma lem5356635 : term380 = term583.
Proof. exact (MK_COMB (@lem5356634) (@lem5356629)). Qed.
Lemma lem5356636 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5356638 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356639 : term380 = term381.
Proof. exact (@lem5356638 (NUMERAL 0) term146). Qed.
Lemma lem5356640 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356641 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356642 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356641 h1) (fun h1 : term381 = True => @lem5356640)). Qed.
Lemma lem5356643 : term381 = True.
Proof. exact (EQ_MP (@lem5356642) (@lem5356640)). Qed.
Lemma lem5356644 : term380 = True.
Proof. exact (TRANS (@lem5356639) (@lem5356643)). Qed.
Lemma lem5356645 : True = term380.
Proof. exact (SYM (@lem5356644)). Qed.
Lemma lem5356646 : term380.
Proof. exact (EQ_MP (@lem5356645) (@lem0)). Qed.
Lemma lem5356647 : term585.
Proof. exact (@lem5356636 (@lem5356646)). Qed.
Lemma lem5356649 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356650 : term380 = term381.
Proof. exact (@lem5356649 (NUMERAL 0) term146). Qed.
Lemma lem5356651 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356652 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356653 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356652 h1) (fun h1 : term381 = True => @lem5356651)). Qed.
Lemma lem5356654 : term381 = True.
Proof. exact (EQ_MP (@lem5356653) (@lem5356651)). Qed.
Lemma lem5356655 : term380 = True.
Proof. exact (TRANS (@lem5356650) (@lem5356654)). Qed.
Lemma lem5356656 : True = term380.
Proof. exact (SYM (@lem5356655)). Qed.
Lemma lem5356657 : term380.
Proof. exact (EQ_MP (@lem5356656) (@lem0)). Qed.
Lemma lem5356658 : term583 = term586.
Proof. exact (@lem5356647 (@lem5356657)). Qed.
Lemma lem5356660 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356661 : term321 = term322.
Proof. exact (@lem5356660 term146 term146). Qed.
Lemma lem5356662 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356663 : term324 = term146.
Proof. exact (EQ_MP (@lem5356662) (@lem940073)). Qed.
Lemma lem5356664 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356665 : term322 = term267.
Proof. exact (MK_COMB (@lem5356664) (@lem5356663)). Qed.
Lemma lem5356666 : term321 = term267.
Proof. exact (TRANS (@lem5356661) (@lem5356665)). Qed.
Lemma lem5356668 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356669 : term392 = term254.
Proof. exact (@lem5356668 term146). Qed.
Lemma lem5356670 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5356671 : term587 = term581.
Proof. exact (MK_COMB (@lem5356670) (@lem5356669)). Qed.
Lemma lem5356672 : term586 = term380.
Proof. exact (MK_COMB (@lem5356671) (@lem5356666)). Qed.
Lemma lem5356674 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356675 : term380 = term381.
Proof. exact (@lem5356674 (NUMERAL 0) term146). Qed.
Lemma lem5356676 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356677 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356678 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356677 h1) (fun h1 : term381 = True => @lem5356676)). Qed.
Lemma lem5356679 : term381 = True.
Proof. exact (EQ_MP (@lem5356678) (@lem5356676)). Qed.
Lemma lem5356680 : term380 = True.
Proof. exact (TRANS (@lem5356675) (@lem5356679)). Qed.
Lemma lem5356681 : term586 = True.
Proof. exact (TRANS (@lem5356672) (@lem5356680)). Qed.
Lemma lem5356682 : term583 = True.
Proof. exact (TRANS (@lem5356658) (@lem5356681)). Qed.
Lemma lem5356683 : term380 = True.
Proof. exact (TRANS (@lem5356635) (@lem5356682)). Qed.
Lemma lem5356684 : term580 = True.
Proof. exact (TRANS (@lem5356626) (@lem5356683)). Qed.
Lemma lem5356685 : True = term580.
Proof. exact (SYM (@lem5356684)). Qed.
Lemma lem5356686 : term580.
Proof. exact (EQ_MP (@lem5356685) (@lem0)). Qed.
Lemma lem5356687 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term594 _69724 _69725.
Proof. exact (conj (@lem5356686) (@lem5356621 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356689 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5356690 (_69724 : int) (_69725 : int) : term595 _69724 _69725.
Proof. exact (@lem5356689 term267 (term336 _69724 _69725)). Qed.
Lemma lem5356691 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term596 _69724 _69725.
Proof. exact (@lem5356690 _69724 _69725 (@lem5356687 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356692 (_69724 : int) (_69725 : int) : (term597 _69724 _69725) = (term336 _69724 _69725).
Proof. exact (@lem1982733 (term336 _69724 _69725)). Qed.
Lemma lem5356693 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5356694 (_69724 : int) (_69725 : int) : (term598 _69724 _69725) = (term339 _69724 _69725).
Proof. exact (MK_COMB (@lem5356693) (@lem5356692 _69724 _69725)). Qed.
Lemma lem5356695 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5356696 (_69724 : int) (_69725 : int) : (term596 _69724 _69725) = (term340 _69724 _69725).
Proof. exact (MK_COMB (@lem5356694 _69724 _69725) (@lem5356695)). Qed.
Lemma lem5356697 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term340 _69724 _69725.
Proof. exact (EQ_MP (@lem5356696 _69724 _69725) (@lem5356691 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356699 (y : real) : term672 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5356700 (_69724 : int) (_69726 : int) : term673 _69724 _69726.
Proof. exact (@lem5356699 (term336 _69724 _69726)). Qed.
Lemma lem5356701 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term674 _69724 _69726.
Proof. exact (@lem5356700 _69724 _69726 (@lem5356623 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356702 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term724 _69724 _69726.
Proof. exact (@lem5356701 _69724 _69725 _69726 h1 term312). Qed.
Lemma lem5356703 (_69724 : int) (_69726 : int) : (term724 _69724 _69726) = ((term725 _69724 _69726) = term254).
Proof. exact (eq_refl (term724 _69724 _69726)). Qed.
Lemma lem5356704 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : (term725 _69724 _69726) = term254.
Proof. exact (EQ_MP (@lem5356703 _69724 _69726) (@lem5356702 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356705 (_69724 : int) (_69726 : int) : (term725 _69724 _69726) = (term726 _69724 _69726).
Proof. exact (@lem1982781 (term337 _69724) term312 (real_of_int _69726)). Qed.
Lemma lem5356706 (_69726 : int) : (term337 _69726) = (term337 _69726).
Proof. exact (eq_refl (term337 _69726)). Qed.
Lemma lem5356707 (_69724 : int) : (term727 _69724) = (term728 _69724).
Proof. exact (@lem1982749 term312 term312 (real_of_int _69724)). Qed.
Lemma lem5356709 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5356710 : term312 = term313.
Proof. exact (@lem5356709 term146). Qed.
Lemma lem5356712 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5356713 : term312 = term313.
Proof. exact (@lem5356712 term146). Qed.
Lemma lem5356714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5356715 : term314 = term315.
Proof. exact (MK_COMB (@lem5356714) (@lem5356713)). Qed.
Lemma lem5356716 : term729 = term730.
Proof. exact (MK_COMB (@lem5356715) (@lem5356710)). Qed.
Lemma lem5356717 : term730 = term731.
Proof. exact (@lem1981613 term312 term312 term267 term267). Qed.
Lemma lem5356719 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356720 : term321 = term322.
Proof. exact (@lem5356719 term146 term146). Qed.
Lemma lem5356721 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356722 : term324 = term146.
Proof. exact (EQ_MP (@lem5356721) (@lem940073)). Qed.
Lemma lem5356723 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356724 : term322 = term267.
Proof. exact (MK_COMB (@lem5356723) (@lem5356722)). Qed.
Lemma lem5356725 : term321 = term267.
Proof. exact (TRANS (@lem5356720) (@lem5356724)). Qed.
Lemma lem5356727 (m : nat) (n : nat) : (term732 m n) = (term320 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5356728 : term729 = term322.
Proof. exact (@lem5356727 term146 term146). Qed.
Lemma lem5356729 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356730 : term324 = term146.
Proof. exact (EQ_MP (@lem5356729) (@lem940073)). Qed.
Lemma lem5356731 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356732 : term322 = term267.
Proof. exact (MK_COMB (@lem5356731) (@lem5356730)). Qed.
Lemma lem5356733 : term729 = term267.
Proof. exact (TRANS (@lem5356728) (@lem5356732)). Qed.
Lemma lem5356734 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5356735 : term733 = term734.
Proof. exact (MK_COMB (@lem5356734) (@lem5356733)). Qed.
Lemma lem5356736 : term731 = term346.
Proof. exact (MK_COMB (@lem5356735) (@lem5356725)). Qed.
Lemma lem5356737 : term730 = term346.
Proof. exact (TRANS (@lem5356717) (@lem5356736)). Qed.
Lemma lem5356738 : term729 = term346.
Proof. exact (TRANS (@lem5356716) (@lem5356737)). Qed.
Lemma lem5356740 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5356741 : term346 = term267.
Proof. exact (@lem5356740 term267). Qed.
Lemma lem5356742 : term729 = term267.
Proof. exact (TRANS (@lem5356738) (@lem5356741)). Qed.
Lemma lem5356743 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5356744 : term735 = term736.
Proof. exact (MK_COMB (@lem5356743) (@lem5356742)). Qed.
Lemma lem5356745 (_69724 : int) : (real_of_int _69724) = (real_of_int _69724).
Proof. exact (eq_refl (real_of_int _69724)). Qed.
Lemma lem5356746 (_69724 : int) : (term728 _69724) = (term737 _69724).
Proof. exact (MK_COMB (@lem5356744) (@lem5356745 _69724)). Qed.
Lemma lem5356747 (_69724 : int) : (term727 _69724) = (term737 _69724).
Proof. exact (TRANS (@lem5356707 _69724) (@lem5356746 _69724)). Qed.
Lemma lem5356748 (_69724 : int) : (term737 _69724) = (real_of_int _69724).
Proof. exact (@lem1982709 (real_of_int _69724)). Qed.
Lemma lem5356749 (_69724 : int) : (term727 _69724) = (real_of_int _69724).
Proof. exact (TRANS (@lem5356747 _69724) (@lem5356748 _69724)). Qed.
Lemma lem5356750 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356751 (_69724 : int) : (term738 _69724) = (term268 _69724).
Proof. exact (MK_COMB (@lem5356750) (@lem5356749 _69724)). Qed.
Lemma lem5356752 (_69724 : int) (_69726 : int) : (term726 _69724 _69726) = (term335 _69724 _69726).
Proof. exact (MK_COMB (@lem5356751 _69724) (@lem5356706 _69726)). Qed.
Lemma lem5356753 (_69724 : int) (_69726 : int) : (term725 _69724 _69726) = (term335 _69724 _69726).
Proof. exact (TRANS (@lem5356705 _69724 _69726) (@lem5356752 _69724 _69726)). Qed.
Lemma lem5356754 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5356755 (_69724 : int) (_69726 : int) : (term739 _69724 _69726) = (term740 _69724 _69726).
Proof. exact (MK_COMB (@lem5356754) (@lem5356753 _69724 _69726)). Qed.
Lemma lem5356756 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5356757 (_69724 : int) (_69726 : int) : ((term725 _69724 _69726) = term254) = ((term335 _69724 _69726) = term254).
Proof. exact (MK_COMB (@lem5356755 _69724 _69726) (@lem5356756)). Qed.
Lemma lem5356758 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : (term335 _69724 _69726) = term254.
Proof. exact (EQ_MP (@lem5356757 _69724 _69726) (@lem5356704 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356759 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term741 _69726 _69724 _69725.
Proof. exact (conj (@lem5356758 _69724 _69725 _69726 h1) (@lem5356697 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356761 (x : real) (y : real) : term677 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5356762 (_69726 : int) (_69724 : int) (_69725 : int) : term742 _69726 _69724 _69725.
Proof. exact (@lem5356761 (term335 _69724 _69726) (term336 _69724 _69725)). Qed.
Lemma lem5356763 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term743 _69726 _69724 _69725.
Proof. exact (@lem5356762 _69726 _69724 _69725 (@lem5356759 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356764 (_69724 : int) (_69726 : int) (_69725 : int) : (term744 _69726 _69724 _69725) = (term745 _69724 _69726 _69725).
Proof. exact (@lem1982753 (real_of_int _69724) (term337 _69724) (term337 _69726) (real_of_int _69725)). Qed.
Lemma lem5356765 (_69724 : int) : (term626 _69724) = (term606 _69724).
Proof. exact (@lem1982715 term312 (real_of_int _69724)). Qed.
Lemma lem5356767 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356768 : term267 = term346.
Proof. exact (@lem5356767 term146). Qed.
Lemma lem5356770 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5356771 : term312 = term313.
Proof. exact (@lem5356770 term146). Qed.
Lemma lem5356772 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356773 : term607 = term608.
Proof. exact (MK_COMB (@lem5356772) (@lem5356771)). Qed.
Lemma lem5356774 : term609 = term610.
Proof. exact (MK_COMB (@lem5356773) (@lem5356768)). Qed.
Lemma lem5356775 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5356777 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356778 : term380 = term381.
Proof. exact (@lem5356777 (NUMERAL 0) term146). Qed.
Lemma lem5356779 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356780 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356781 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356780 h1) (fun h1 : term381 = True => @lem5356779)). Qed.
Lemma lem5356782 : term381 = True.
Proof. exact (EQ_MP (@lem5356781) (@lem5356779)). Qed.
Lemma lem5356783 : term380 = True.
Proof. exact (TRANS (@lem5356778) (@lem5356782)). Qed.
Lemma lem5356784 : True = term380.
Proof. exact (SYM (@lem5356783)). Qed.
Lemma lem5356785 : term380.
Proof. exact (EQ_MP (@lem5356784) (@lem0)). Qed.
Lemma lem5356786 : term612.
Proof. exact (@lem5356775 (@lem5356785)). Qed.
Lemma lem5356788 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356789 : term380 = term381.
Proof. exact (@lem5356788 (NUMERAL 0) term146). Qed.
Lemma lem5356790 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356791 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356792 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356791 h1) (fun h1 : term381 = True => @lem5356790)). Qed.
Lemma lem5356793 : term381 = True.
Proof. exact (EQ_MP (@lem5356792) (@lem5356790)). Qed.
Lemma lem5356794 : term380 = True.
Proof. exact (TRANS (@lem5356789) (@lem5356793)). Qed.
Lemma lem5356795 : True = term380.
Proof. exact (SYM (@lem5356794)). Qed.
Lemma lem5356796 : term380.
Proof. exact (EQ_MP (@lem5356795) (@lem0)). Qed.
Lemma lem5356797 : term613.
Proof. exact (@lem5356786 (@lem5356796)). Qed.
Lemma lem5356799 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356800 : term380 = term381.
Proof. exact (@lem5356799 (NUMERAL 0) term146). Qed.
Lemma lem5356801 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356802 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356803 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356802 h1) (fun h1 : term381 = True => @lem5356801)). Qed.
Lemma lem5356804 : term381 = True.
Proof. exact (EQ_MP (@lem5356803) (@lem5356801)). Qed.
Lemma lem5356805 : term380 = True.
Proof. exact (TRANS (@lem5356800) (@lem5356804)). Qed.
Lemma lem5356806 : True = term380.
Proof. exact (SYM (@lem5356805)). Qed.
Lemma lem5356807 : term380.
Proof. exact (EQ_MP (@lem5356806) (@lem0)). Qed.
Lemma lem5356808 : term614.
Proof. exact (@lem5356797 (@lem5356807)). Qed.
Lemma lem5356810 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356811 : term321 = term322.
Proof. exact (@lem5356810 term146 term146). Qed.
Lemma lem5356812 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356813 : term324 = term146.
Proof. exact (EQ_MP (@lem5356812) (@lem940073)). Qed.
Lemma lem5356814 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356815 : term322 = term267.
Proof. exact (MK_COMB (@lem5356814) (@lem5356813)). Qed.
Lemma lem5356816 : term321 = term267.
Proof. exact (TRANS (@lem5356811) (@lem5356815)). Qed.
Lemma lem5356818 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5356819 : term347 = term352.
Proof. exact (@lem5356818 term146 term146). Qed.
Lemma lem5356820 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356821 : term324 = term146.
Proof. exact (EQ_MP (@lem5356820) (@lem940073)). Qed.
Lemma lem5356822 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356823 : term322 = term267.
Proof. exact (MK_COMB (@lem5356822) (@lem5356821)). Qed.
Lemma lem5356824 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5356825 : term352 = term312.
Proof. exact (MK_COMB (@lem5356824) (@lem5356823)). Qed.
Lemma lem5356826 : term347 = term312.
Proof. exact (TRANS (@lem5356819) (@lem5356825)). Qed.
Lemma lem5356827 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356828 : term615 = term607.
Proof. exact (MK_COMB (@lem5356827) (@lem5356826)). Qed.
Lemma lem5356829 : term616 = term609.
Proof. exact (MK_COMB (@lem5356828) (@lem5356816)). Qed.
Lemma lem5356831 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5356832 : term609 = term254.
Proof. exact (@lem5356831 term146). Qed.
Lemma lem5356833 : term616 = term254.
Proof. exact (TRANS (@lem5356829) (@lem5356832)). Qed.
Lemma lem5356834 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5356835 : term618 = term390.
Proof. exact (MK_COMB (@lem5356834) (@lem5356833)). Qed.
Lemma lem5356836 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5356837 : term619 = term392.
Proof. exact (MK_COMB (@lem5356835) (@lem5356836)). Qed.
Lemma lem5356839 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356840 : term392 = term254.
Proof. exact (@lem5356839 term146). Qed.
Lemma lem5356841 : term619 = term254.
Proof. exact (TRANS (@lem5356837) (@lem5356840)). Qed.
Lemma lem5356843 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356844 : term321 = term322.
Proof. exact (@lem5356843 term146 term146). Qed.
Lemma lem5356845 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356846 : term324 = term146.
Proof. exact (EQ_MP (@lem5356845) (@lem940073)). Qed.
Lemma lem5356847 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356848 : term322 = term267.
Proof. exact (MK_COMB (@lem5356847) (@lem5356846)). Qed.
Lemma lem5356849 : term321 = term267.
Proof. exact (TRANS (@lem5356844) (@lem5356848)). Qed.
Lemma lem5356850 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5356851 : term394 = term392.
Proof. exact (MK_COMB (@lem5356850) (@lem5356849)). Qed.
Lemma lem5356853 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356854 : term392 = term254.
Proof. exact (@lem5356853 term146). Qed.
Lemma lem5356855 : term394 = term254.
Proof. exact (TRANS (@lem5356851) (@lem5356854)). Qed.
Lemma lem5356856 : term254 = term394.
Proof. exact (SYM (@lem5356855)). Qed.
Lemma lem5356857 : term619 = term394.
Proof. exact (TRANS (@lem5356841) (@lem5356856)). Qed.
Lemma lem5356858 : term610 = term309.
Proof. exact (@lem5356808 (@lem5356857)). Qed.
Lemma lem5356859 : term609 = term309.
Proof. exact (TRANS (@lem5356774) (@lem5356858)). Qed.
Lemma lem5356861 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5356862 : term309 = term254.
Proof. exact (@lem5356861 term254). Qed.
Lemma lem5356863 : term609 = term254.
Proof. exact (TRANS (@lem5356859) (@lem5356862)). Qed.
Lemma lem5356864 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5356865 : term620 = term390.
Proof. exact (MK_COMB (@lem5356864) (@lem5356863)). Qed.
Lemma lem5356866 (_69724 : int) : (real_of_int _69724) = (real_of_int _69724).
Proof. exact (eq_refl (real_of_int _69724)). Qed.
Lemma lem5356867 (_69724 : int) : (term606 _69724) = (term621 _69724).
Proof. exact (MK_COMB (@lem5356865) (@lem5356866 _69724)). Qed.
Lemma lem5356868 (_69724 : int) : (term626 _69724) = (term621 _69724).
Proof. exact (TRANS (@lem5356765 _69724) (@lem5356867 _69724)). Qed.
Lemma lem5356869 (_69724 : int) : (term621 _69724) = term254.
Proof. exact (@lem1982719 (real_of_int _69724)). Qed.
Lemma lem5356870 (_69724 : int) : (term626 _69724) = term254.
Proof. exact (TRANS (@lem5356868 _69724) (@lem5356869 _69724)). Qed.
Lemma lem5356871 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5356872 (_69724 : int) : (term627 _69724) = term623.
Proof. exact (MK_COMB (@lem5356871) (@lem5356870 _69724)). Qed.
Lemma lem5356873 (_69725 : int) (_69726 : int) : (term336 _69726 _69725) = (term335 _69725 _69726).
Proof. exact (@lem1982761 (real_of_int _69725) (term337 _69726)). Qed.
Lemma lem5356874 (_69724 : int) (_69725 : int) (_69726 : int) : (term745 _69724 _69726 _69725) = (term746 _69725 _69726).
Proof. exact (MK_COMB (@lem5356872 _69724) (@lem5356873 _69725 _69726)). Qed.
Lemma lem5356875 (_69724 : int) (_69725 : int) (_69726 : int) : (term744 _69726 _69724 _69725) = (term746 _69725 _69726).
Proof. exact (TRANS (@lem5356764 _69724 _69726 _69725) (@lem5356874 _69724 _69725 _69726)). Qed.
Lemma lem5356876 (_69725 : int) (_69726 : int) : (term746 _69725 _69726) = (term335 _69725 _69726).
Proof. exact (@lem1982721 (term335 _69725 _69726)). Qed.
Lemma lem5356877 (_69724 : int) (_69725 : int) (_69726 : int) : (term744 _69726 _69724 _69725) = (term335 _69725 _69726).
Proof. exact (TRANS (@lem5356875 _69724 _69725 _69726) (@lem5356876 _69725 _69726)). Qed.
Lemma lem5356878 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5356879 (_69724 : int) (_69725 : int) (_69726 : int) : (term747 _69726 _69724 _69725) = (term397 _69725 _69726).
Proof. exact (MK_COMB (@lem5356878) (@lem5356877 _69724 _69725 _69726)). Qed.
Lemma lem5356880 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5356881 (_69724 : int) (_69725 : int) (_69726 : int) : (term743 _69726 _69724 _69725) = (term398 _69725 _69726).
Proof. exact (MK_COMB (@lem5356879 _69724 _69725 _69726) (@lem5356880)). Qed.
Lemma lem5356882 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term398 _69725 _69726.
Proof. exact (EQ_MP (@lem5356881 _69724 _69725 _69726) (@lem5356763 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356884 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5356885 : term580 = term380.
Proof. exact (@lem5356884 term254 term267). Qed.
Lemma lem5356887 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356888 : term267 = term346.
Proof. exact (@lem5356887 term146). Qed.
Lemma lem5356890 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356891 : term254 = term309.
Proof. exact (@lem5356890 (NUMERAL 0)). Qed.
Lemma lem5356892 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5356893 : term581 = term582.
Proof. exact (MK_COMB (@lem5356892) (@lem5356891)). Qed.
Lemma lem5356894 : term380 = term583.
Proof. exact (MK_COMB (@lem5356893) (@lem5356888)). Qed.
Lemma lem5356895 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5356897 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356898 : term380 = term381.
Proof. exact (@lem5356897 (NUMERAL 0) term146). Qed.
Lemma lem5356899 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356900 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356901 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356900 h1) (fun h1 : term381 = True => @lem5356899)). Qed.
Lemma lem5356902 : term381 = True.
Proof. exact (EQ_MP (@lem5356901) (@lem5356899)). Qed.
Lemma lem5356903 : term380 = True.
Proof. exact (TRANS (@lem5356898) (@lem5356902)). Qed.
Lemma lem5356904 : True = term380.
Proof. exact (SYM (@lem5356903)). Qed.
Lemma lem5356905 : term380.
Proof. exact (EQ_MP (@lem5356904) (@lem0)). Qed.
Lemma lem5356906 : term585.
Proof. exact (@lem5356895 (@lem5356905)). Qed.
Lemma lem5356908 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356909 : term380 = term381.
Proof. exact (@lem5356908 (NUMERAL 0) term146). Qed.
Lemma lem5356910 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356911 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356912 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356911 h1) (fun h1 : term381 = True => @lem5356910)). Qed.
Lemma lem5356913 : term381 = True.
Proof. exact (EQ_MP (@lem5356912) (@lem5356910)). Qed.
Lemma lem5356914 : term380 = True.
Proof. exact (TRANS (@lem5356909) (@lem5356913)). Qed.
Lemma lem5356915 : True = term380.
Proof. exact (SYM (@lem5356914)). Qed.
Lemma lem5356916 : term380.
Proof. exact (EQ_MP (@lem5356915) (@lem0)). Qed.
Lemma lem5356917 : term583 = term586.
Proof. exact (@lem5356906 (@lem5356916)). Qed.
Lemma lem5356919 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356920 : term321 = term322.
Proof. exact (@lem5356919 term146 term146). Qed.
Lemma lem5356921 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356922 : term324 = term146.
Proof. exact (EQ_MP (@lem5356921) (@lem940073)). Qed.
Lemma lem5356923 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356924 : term322 = term267.
Proof. exact (MK_COMB (@lem5356923) (@lem5356922)). Qed.
Lemma lem5356925 : term321 = term267.
Proof. exact (TRANS (@lem5356920) (@lem5356924)). Qed.
Lemma lem5356927 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5356928 : term392 = term254.
Proof. exact (@lem5356927 term146). Qed.
Lemma lem5356929 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5356930 : term587 = term581.
Proof. exact (MK_COMB (@lem5356929) (@lem5356928)). Qed.
Lemma lem5356931 : term586 = term380.
Proof. exact (MK_COMB (@lem5356930) (@lem5356925)). Qed.
Lemma lem5356933 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356934 : term380 = term381.
Proof. exact (@lem5356933 (NUMERAL 0) term146). Qed.
Lemma lem5356935 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356936 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356937 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356936 h1) (fun h1 : term381 = True => @lem5356935)). Qed.
Lemma lem5356938 : term381 = True.
Proof. exact (EQ_MP (@lem5356937) (@lem5356935)). Qed.
Lemma lem5356939 : term380 = True.
Proof. exact (TRANS (@lem5356934) (@lem5356938)). Qed.
Lemma lem5356940 : term586 = True.
Proof. exact (TRANS (@lem5356931) (@lem5356939)). Qed.
Lemma lem5356941 : term583 = True.
Proof. exact (TRANS (@lem5356917) (@lem5356940)). Qed.
Lemma lem5356942 : term380 = True.
Proof. exact (TRANS (@lem5356894) (@lem5356941)). Qed.
Lemma lem5356943 : term580 = True.
Proof. exact (TRANS (@lem5356885) (@lem5356942)). Qed.
Lemma lem5356944 : True = term580.
Proof. exact (SYM (@lem5356943)). Qed.
Lemma lem5356945 : term580.
Proof. exact (EQ_MP (@lem5356944) (@lem0)). Qed.
Lemma lem5356946 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term649 _69725 _69726.
Proof. exact (conj (@lem5356945) (@lem5356882 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356948 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5356949 (_69725 : int) (_69726 : int) : term650 _69725 _69726.
Proof. exact (@lem5356948 term267 (term335 _69725 _69726)). Qed.
Lemma lem5356950 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term651 _69725 _69726.
Proof. exact (@lem5356949 _69725 _69726 (@lem5356946 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356951 (_69725 : int) (_69726 : int) : (term652 _69725 _69726) = (term335 _69725 _69726).
Proof. exact (@lem1982733 (term335 _69725 _69726)). Qed.
Lemma lem5356952 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5356953 (_69725 : int) (_69726 : int) : (term653 _69725 _69726) = (term397 _69725 _69726).
Proof. exact (MK_COMB (@lem5356952) (@lem5356951 _69725 _69726)). Qed.
Lemma lem5356954 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5356955 (_69725 : int) (_69726 : int) : (term651 _69725 _69726) = (term398 _69725 _69726).
Proof. exact (MK_COMB (@lem5356953 _69725 _69726) (@lem5356954)). Qed.
Lemma lem5356956 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term398 _69725 _69726.
Proof. exact (EQ_MP (@lem5356955 _69725 _69726) (@lem5356950 _69724 _69725 _69726 h1)). Qed.
Lemma lem5356958 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5356959 : term580 = term380.
Proof. exact (@lem5356958 term254 term267). Qed.
Lemma lem5356961 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356962 : term267 = term346.
Proof. exact (@lem5356961 term146). Qed.
Lemma lem5356964 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5356965 : term254 = term309.
Proof. exact (@lem5356964 (NUMERAL 0)). Qed.
Lemma lem5356966 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5356967 : term581 = term582.
Proof. exact (MK_COMB (@lem5356966) (@lem5356965)). Qed.
Lemma lem5356968 : term380 = term583.
Proof. exact (MK_COMB (@lem5356967) (@lem5356962)). Qed.
Lemma lem5356969 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5356971 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356972 : term380 = term381.
Proof. exact (@lem5356971 (NUMERAL 0) term146). Qed.
Lemma lem5356973 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356974 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356975 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356974 h1) (fun h1 : term381 = True => @lem5356973)). Qed.
Lemma lem5356976 : term381 = True.
Proof. exact (EQ_MP (@lem5356975) (@lem5356973)). Qed.
Lemma lem5356977 : term380 = True.
Proof. exact (TRANS (@lem5356972) (@lem5356976)). Qed.
Lemma lem5356978 : True = term380.
Proof. exact (SYM (@lem5356977)). Qed.
Lemma lem5356979 : term380.
Proof. exact (EQ_MP (@lem5356978) (@lem0)). Qed.
Lemma lem5356980 : term585.
Proof. exact (@lem5356969 (@lem5356979)). Qed.
Lemma lem5356982 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5356983 : term380 = term381.
Proof. exact (@lem5356982 (NUMERAL 0) term146). Qed.
Lemma lem5356984 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5356985 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5356986 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5356985 h1) (fun h1 : term381 = True => @lem5356984)). Qed.
Lemma lem5356987 : term381 = True.
Proof. exact (EQ_MP (@lem5356986) (@lem5356984)). Qed.
Lemma lem5356988 : term380 = True.
Proof. exact (TRANS (@lem5356983) (@lem5356987)). Qed.
Lemma lem5356989 : True = term380.
Proof. exact (SYM (@lem5356988)). Qed.
Lemma lem5356990 : term380.
Proof. exact (EQ_MP (@lem5356989) (@lem0)). Qed.
Lemma lem5356991 : term583 = term586.
Proof. exact (@lem5356980 (@lem5356990)). Qed.
Lemma lem5356993 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5356994 : term321 = term322.
Proof. exact (@lem5356993 term146 term146). Qed.
Lemma lem5356995 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5356996 : term324 = term146.
Proof. exact (EQ_MP (@lem5356995) (@lem940073)). Qed.
Lemma lem5356997 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5356998 : term322 = term267.
Proof. exact (MK_COMB (@lem5356997) (@lem5356996)). Qed.
Lemma lem5356999 : term321 = term267.
Proof. exact (TRANS (@lem5356994) (@lem5356998)). Qed.
Lemma lem5357001 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357002 : term392 = term254.
Proof. exact (@lem5357001 term146). Qed.
Lemma lem5357003 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5357004 : term587 = term581.
Proof. exact (MK_COMB (@lem5357003) (@lem5357002)). Qed.
Lemma lem5357005 : term586 = term380.
Proof. exact (MK_COMB (@lem5357004) (@lem5356999)). Qed.
Lemma lem5357007 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357008 : term380 = term381.
Proof. exact (@lem5357007 (NUMERAL 0) term146). Qed.
Lemma lem5357009 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357010 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357011 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357010 h1) (fun h1 : term381 = True => @lem5357009)). Qed.
Lemma lem5357012 : term381 = True.
Proof. exact (EQ_MP (@lem5357011) (@lem5357009)). Qed.
Lemma lem5357013 : term380 = True.
Proof. exact (TRANS (@lem5357008) (@lem5357012)). Qed.
Lemma lem5357014 : term586 = True.
Proof. exact (TRANS (@lem5357005) (@lem5357013)). Qed.
Lemma lem5357015 : term583 = True.
Proof. exact (TRANS (@lem5356991) (@lem5357014)). Qed.
Lemma lem5357016 : term380 = True.
Proof. exact (TRANS (@lem5356968) (@lem5357015)). Qed.
Lemma lem5357017 : term580 = True.
Proof. exact (TRANS (@lem5356959) (@lem5357016)). Qed.
Lemma lem5357018 : True = term580.
Proof. exact (SYM (@lem5357017)). Qed.
Lemma lem5357019 : term580.
Proof. exact (EQ_MP (@lem5357018) (@lem0)). Qed.
Lemma lem5357020 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term644 _69725 _69726.
Proof. exact (conj (@lem5357019) (@lem5356622 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357022 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5357023 (_69725 : int) (_69726 : int) : term645 _69725 _69726.
Proof. exact (@lem5357022 term267 (term361 _69725 _69726)). Qed.
Lemma lem5357024 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term646 _69725 _69726.
Proof. exact (@lem5357023 _69725 _69726 (@lem5357020 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357025 (_69725 : int) (_69726 : int) : (term647 _69725 _69726) = (term361 _69725 _69726).
Proof. exact (@lem1982733 (term361 _69725 _69726)). Qed.
Lemma lem5357026 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5357027 (_69725 : int) (_69726 : int) : (term648 _69725 _69726) = (term362 _69725 _69726).
Proof. exact (MK_COMB (@lem5357026) (@lem5357025 _69725 _69726)). Qed.
Lemma lem5357028 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5357029 (_69725 : int) (_69726 : int) : (term646 _69725 _69726) = (term363 _69725 _69726).
Proof. exact (MK_COMB (@lem5357027 _69725 _69726) (@lem5357028)). Qed.
Lemma lem5357030 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term363 _69725 _69726.
Proof. exact (EQ_MP (@lem5357029 _69725 _69726) (@lem5357024 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357031 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term449 _69725 _69726.
Proof. exact (conj (@lem5357030 _69724 _69725 _69726 h1) (@lem5356956 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357033 (x : real) (y : real) : term600 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5357034 (_69725 : int) (_69726 : int) : term664 _69725 _69726.
Proof. exact (@lem5357033 (term361 _69725 _69726) (term335 _69725 _69726)). Qed.
Lemma lem5357035 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term665 _69725 _69726.
Proof. exact (@lem5357034 _69725 _69726 (@lem5357031 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357036 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = (term667 _69725 _69726).
Proof. exact (@lem1982753 (term337 _69725) (real_of_int _69725) (term659 _69726) (term337 _69726)). Qed.
Lemma lem5357037 (_69725 : int) : (term605 _69725) = (term606 _69725).
Proof. exact (@lem1982713 term312 (real_of_int _69725)). Qed.
Lemma lem5357039 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5357040 : term267 = term346.
Proof. exact (@lem5357039 term146). Qed.
Lemma lem5357042 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5357043 : term312 = term313.
Proof. exact (@lem5357042 term146). Qed.
Lemma lem5357044 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357045 : term607 = term608.
Proof. exact (MK_COMB (@lem5357044) (@lem5357043)). Qed.
Lemma lem5357046 : term609 = term610.
Proof. exact (MK_COMB (@lem5357045) (@lem5357040)). Qed.
Lemma lem5357047 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5357049 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357050 : term380 = term381.
Proof. exact (@lem5357049 (NUMERAL 0) term146). Qed.
Lemma lem5357051 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357052 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357053 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357052 h1) (fun h1 : term381 = True => @lem5357051)). Qed.
Lemma lem5357054 : term381 = True.
Proof. exact (EQ_MP (@lem5357053) (@lem5357051)). Qed.
Lemma lem5357055 : term380 = True.
Proof. exact (TRANS (@lem5357050) (@lem5357054)). Qed.
Lemma lem5357056 : True = term380.
Proof. exact (SYM (@lem5357055)). Qed.
Lemma lem5357057 : term380.
Proof. exact (EQ_MP (@lem5357056) (@lem0)). Qed.
Lemma lem5357058 : term612.
Proof. exact (@lem5357047 (@lem5357057)). Qed.
Lemma lem5357060 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357061 : term380 = term381.
Proof. exact (@lem5357060 (NUMERAL 0) term146). Qed.
Lemma lem5357062 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357063 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357064 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357063 h1) (fun h1 : term381 = True => @lem5357062)). Qed.
Lemma lem5357065 : term381 = True.
Proof. exact (EQ_MP (@lem5357064) (@lem5357062)). Qed.
Lemma lem5357066 : term380 = True.
Proof. exact (TRANS (@lem5357061) (@lem5357065)). Qed.
Lemma lem5357067 : True = term380.
Proof. exact (SYM (@lem5357066)). Qed.
Lemma lem5357068 : term380.
Proof. exact (EQ_MP (@lem5357067) (@lem0)). Qed.
Lemma lem5357069 : term613.
Proof. exact (@lem5357058 (@lem5357068)). Qed.
Lemma lem5357071 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357072 : term380 = term381.
Proof. exact (@lem5357071 (NUMERAL 0) term146). Qed.
Lemma lem5357073 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357074 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357075 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357074 h1) (fun h1 : term381 = True => @lem5357073)). Qed.
Lemma lem5357076 : term381 = True.
Proof. exact (EQ_MP (@lem5357075) (@lem5357073)). Qed.
Lemma lem5357077 : term380 = True.
Proof. exact (TRANS (@lem5357072) (@lem5357076)). Qed.
Lemma lem5357078 : True = term380.
Proof. exact (SYM (@lem5357077)). Qed.
Lemma lem5357079 : term380.
Proof. exact (EQ_MP (@lem5357078) (@lem0)). Qed.
Lemma lem5357080 : term614.
Proof. exact (@lem5357069 (@lem5357079)). Qed.
Lemma lem5357082 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5357083 : term321 = term322.
Proof. exact (@lem5357082 term146 term146). Qed.
Lemma lem5357084 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357085 : term324 = term146.
Proof. exact (EQ_MP (@lem5357084) (@lem940073)). Qed.
Lemma lem5357086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357087 : term322 = term267.
Proof. exact (MK_COMB (@lem5357086) (@lem5357085)). Qed.
Lemma lem5357088 : term321 = term267.
Proof. exact (TRANS (@lem5357083) (@lem5357087)). Qed.
Lemma lem5357090 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5357091 : term347 = term352.
Proof. exact (@lem5357090 term146 term146). Qed.
Lemma lem5357092 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357093 : term324 = term146.
Proof. exact (EQ_MP (@lem5357092) (@lem940073)). Qed.
Lemma lem5357094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357095 : term322 = term267.
Proof. exact (MK_COMB (@lem5357094) (@lem5357093)). Qed.
Lemma lem5357096 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5357097 : term352 = term312.
Proof. exact (MK_COMB (@lem5357096) (@lem5357095)). Qed.
Lemma lem5357098 : term347 = term312.
Proof. exact (TRANS (@lem5357091) (@lem5357097)). Qed.
Lemma lem5357099 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357100 : term615 = term607.
Proof. exact (MK_COMB (@lem5357099) (@lem5357098)). Qed.
Lemma lem5357101 : term616 = term609.
Proof. exact (MK_COMB (@lem5357100) (@lem5357088)). Qed.
Lemma lem5357103 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5357104 : term609 = term254.
Proof. exact (@lem5357103 term146). Qed.
Lemma lem5357105 : term616 = term254.
Proof. exact (TRANS (@lem5357101) (@lem5357104)). Qed.
Lemma lem5357106 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5357107 : term618 = term390.
Proof. exact (MK_COMB (@lem5357106) (@lem5357105)). Qed.
Lemma lem5357108 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5357109 : term619 = term392.
Proof. exact (MK_COMB (@lem5357107) (@lem5357108)). Qed.
Lemma lem5357111 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357112 : term392 = term254.
Proof. exact (@lem5357111 term146). Qed.
Lemma lem5357113 : term619 = term254.
Proof. exact (TRANS (@lem5357109) (@lem5357112)). Qed.
Lemma lem5357115 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5357116 : term321 = term322.
Proof. exact (@lem5357115 term146 term146). Qed.
Lemma lem5357117 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357118 : term324 = term146.
Proof. exact (EQ_MP (@lem5357117) (@lem940073)). Qed.
Lemma lem5357119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357120 : term322 = term267.
Proof. exact (MK_COMB (@lem5357119) (@lem5357118)). Qed.
Lemma lem5357121 : term321 = term267.
Proof. exact (TRANS (@lem5357116) (@lem5357120)). Qed.
Lemma lem5357122 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5357123 : term394 = term392.
Proof. exact (MK_COMB (@lem5357122) (@lem5357121)). Qed.
Lemma lem5357125 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357126 : term392 = term254.
Proof. exact (@lem5357125 term146). Qed.
Lemma lem5357127 : term394 = term254.
Proof. exact (TRANS (@lem5357123) (@lem5357126)). Qed.
Lemma lem5357128 : term254 = term394.
Proof. exact (SYM (@lem5357127)). Qed.
Lemma lem5357129 : term619 = term394.
Proof. exact (TRANS (@lem5357113) (@lem5357128)). Qed.
Lemma lem5357130 : term610 = term309.
Proof. exact (@lem5357080 (@lem5357129)). Qed.
Lemma lem5357131 : term609 = term309.
Proof. exact (TRANS (@lem5357046) (@lem5357130)). Qed.
Lemma lem5357133 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5357134 : term309 = term254.
Proof. exact (@lem5357133 term254). Qed.
Lemma lem5357135 : term609 = term254.
Proof. exact (TRANS (@lem5357131) (@lem5357134)). Qed.
Lemma lem5357136 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5357137 : term620 = term390.
Proof. exact (MK_COMB (@lem5357136) (@lem5357135)). Qed.
Lemma lem5357138 (_69725 : int) : (real_of_int _69725) = (real_of_int _69725).
Proof. exact (eq_refl (real_of_int _69725)). Qed.
Lemma lem5357139 (_69725 : int) : (term606 _69725) = (term621 _69725).
Proof. exact (MK_COMB (@lem5357137) (@lem5357138 _69725)). Qed.
Lemma lem5357140 (_69725 : int) : (term605 _69725) = (term621 _69725).
Proof. exact (TRANS (@lem5357037 _69725) (@lem5357139 _69725)). Qed.
Lemma lem5357141 (_69725 : int) : (term621 _69725) = term254.
Proof. exact (@lem1982719 (real_of_int _69725)). Qed.
Lemma lem5357142 (_69725 : int) : (term605 _69725) = term254.
Proof. exact (TRANS (@lem5357140 _69725) (@lem5357141 _69725)). Qed.
Lemma lem5357143 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357144 (_69725 : int) : (term622 _69725) = term623.
Proof. exact (MK_COMB (@lem5357143) (@lem5357142 _69725)). Qed.
Lemma lem5357145 (_69726 : int) : (term668 _69726) = (term625 _69726).
Proof. exact (@lem1982759 (real_of_int _69726) (term337 _69726) term312). Qed.
Lemma lem5357146 (_69726 : int) : (term626 _69726) = (term606 _69726).
Proof. exact (@lem1982715 term312 (real_of_int _69726)). Qed.
Lemma lem5357148 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5357149 : term267 = term346.
Proof. exact (@lem5357148 term146). Qed.
Lemma lem5357151 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5357152 : term312 = term313.
Proof. exact (@lem5357151 term146). Qed.
Lemma lem5357153 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357154 : term607 = term608.
Proof. exact (MK_COMB (@lem5357153) (@lem5357152)). Qed.
Lemma lem5357155 : term609 = term610.
Proof. exact (MK_COMB (@lem5357154) (@lem5357149)). Qed.
Lemma lem5357156 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5357158 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357159 : term380 = term381.
Proof. exact (@lem5357158 (NUMERAL 0) term146). Qed.
Lemma lem5357160 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357161 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357162 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357161 h1) (fun h1 : term381 = True => @lem5357160)). Qed.
Lemma lem5357163 : term381 = True.
Proof. exact (EQ_MP (@lem5357162) (@lem5357160)). Qed.
Lemma lem5357164 : term380 = True.
Proof. exact (TRANS (@lem5357159) (@lem5357163)). Qed.
Lemma lem5357165 : True = term380.
Proof. exact (SYM (@lem5357164)). Qed.
Lemma lem5357166 : term380.
Proof. exact (EQ_MP (@lem5357165) (@lem0)). Qed.
Lemma lem5357167 : term612.
Proof. exact (@lem5357156 (@lem5357166)). Qed.
Lemma lem5357169 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357170 : term380 = term381.
Proof. exact (@lem5357169 (NUMERAL 0) term146). Qed.
Lemma lem5357171 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357172 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357173 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357172 h1) (fun h1 : term381 = True => @lem5357171)). Qed.
Lemma lem5357174 : term381 = True.
Proof. exact (EQ_MP (@lem5357173) (@lem5357171)). Qed.
Lemma lem5357175 : term380 = True.
Proof. exact (TRANS (@lem5357170) (@lem5357174)). Qed.
Lemma lem5357176 : True = term380.
Proof. exact (SYM (@lem5357175)). Qed.
Lemma lem5357177 : term380.
Proof. exact (EQ_MP (@lem5357176) (@lem0)). Qed.
Lemma lem5357178 : term613.
Proof. exact (@lem5357167 (@lem5357177)). Qed.
Lemma lem5357180 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357181 : term380 = term381.
Proof. exact (@lem5357180 (NUMERAL 0) term146). Qed.
Lemma lem5357182 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357183 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357184 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357183 h1) (fun h1 : term381 = True => @lem5357182)). Qed.
Lemma lem5357185 : term381 = True.
Proof. exact (EQ_MP (@lem5357184) (@lem5357182)). Qed.
Lemma lem5357186 : term380 = True.
Proof. exact (TRANS (@lem5357181) (@lem5357185)). Qed.
Lemma lem5357187 : True = term380.
Proof. exact (SYM (@lem5357186)). Qed.
Lemma lem5357188 : term380.
Proof. exact (EQ_MP (@lem5357187) (@lem0)). Qed.
Lemma lem5357189 : term614.
Proof. exact (@lem5357178 (@lem5357188)). Qed.
Lemma lem5357191 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5357192 : term321 = term322.
Proof. exact (@lem5357191 term146 term146). Qed.
Lemma lem5357193 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357194 : term324 = term146.
Proof. exact (EQ_MP (@lem5357193) (@lem940073)). Qed.
Lemma lem5357195 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357196 : term322 = term267.
Proof. exact (MK_COMB (@lem5357195) (@lem5357194)). Qed.
Lemma lem5357197 : term321 = term267.
Proof. exact (TRANS (@lem5357192) (@lem5357196)). Qed.
Lemma lem5357199 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5357200 : term347 = term352.
Proof. exact (@lem5357199 term146 term146). Qed.
Lemma lem5357201 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357202 : term324 = term146.
Proof. exact (EQ_MP (@lem5357201) (@lem940073)). Qed.
Lemma lem5357203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357204 : term322 = term267.
Proof. exact (MK_COMB (@lem5357203) (@lem5357202)). Qed.
Lemma lem5357205 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5357206 : term352 = term312.
Proof. exact (MK_COMB (@lem5357205) (@lem5357204)). Qed.
Lemma lem5357207 : term347 = term312.
Proof. exact (TRANS (@lem5357200) (@lem5357206)). Qed.
Lemma lem5357208 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357209 : term615 = term607.
Proof. exact (MK_COMB (@lem5357208) (@lem5357207)). Qed.
Lemma lem5357210 : term616 = term609.
Proof. exact (MK_COMB (@lem5357209) (@lem5357197)). Qed.
Lemma lem5357212 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5357213 : term609 = term254.
Proof. exact (@lem5357212 term146). Qed.
Lemma lem5357214 : term616 = term254.
Proof. exact (TRANS (@lem5357210) (@lem5357213)). Qed.
Lemma lem5357215 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5357216 : term618 = term390.
Proof. exact (MK_COMB (@lem5357215) (@lem5357214)). Qed.
Lemma lem5357217 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5357218 : term619 = term392.
Proof. exact (MK_COMB (@lem5357216) (@lem5357217)). Qed.
Lemma lem5357220 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357221 : term392 = term254.
Proof. exact (@lem5357220 term146). Qed.
Lemma lem5357222 : term619 = term254.
Proof. exact (TRANS (@lem5357218) (@lem5357221)). Qed.
Lemma lem5357224 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5357225 : term321 = term322.
Proof. exact (@lem5357224 term146 term146). Qed.
Lemma lem5357226 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357227 : term324 = term146.
Proof. exact (EQ_MP (@lem5357226) (@lem940073)). Qed.
Lemma lem5357228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357229 : term322 = term267.
Proof. exact (MK_COMB (@lem5357228) (@lem5357227)). Qed.
Lemma lem5357230 : term321 = term267.
Proof. exact (TRANS (@lem5357225) (@lem5357229)). Qed.
Lemma lem5357231 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5357232 : term394 = term392.
Proof. exact (MK_COMB (@lem5357231) (@lem5357230)). Qed.
Lemma lem5357234 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357235 : term392 = term254.
Proof. exact (@lem5357234 term146). Qed.
Lemma lem5357236 : term394 = term254.
Proof. exact (TRANS (@lem5357232) (@lem5357235)). Qed.
Lemma lem5357237 : term254 = term394.
Proof. exact (SYM (@lem5357236)). Qed.
Lemma lem5357238 : term619 = term394.
Proof. exact (TRANS (@lem5357222) (@lem5357237)). Qed.
Lemma lem5357239 : term610 = term309.
Proof. exact (@lem5357189 (@lem5357238)). Qed.
Lemma lem5357240 : term609 = term309.
Proof. exact (TRANS (@lem5357155) (@lem5357239)). Qed.
Lemma lem5357242 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5357243 : term309 = term254.
Proof. exact (@lem5357242 term254). Qed.
Lemma lem5357244 : term609 = term254.
Proof. exact (TRANS (@lem5357240) (@lem5357243)). Qed.
Lemma lem5357245 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5357246 : term620 = term390.
Proof. exact (MK_COMB (@lem5357245) (@lem5357244)). Qed.
Lemma lem5357247 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5357248 (_69726 : int) : (term606 _69726) = (term621 _69726).
Proof. exact (MK_COMB (@lem5357246) (@lem5357247 _69726)). Qed.
Lemma lem5357249 (_69726 : int) : (term626 _69726) = (term621 _69726).
Proof. exact (TRANS (@lem5357146 _69726) (@lem5357248 _69726)). Qed.
Lemma lem5357250 (_69726 : int) : (term621 _69726) = term254.
Proof. exact (@lem1982719 (real_of_int _69726)). Qed.
Lemma lem5357251 (_69726 : int) : (term626 _69726) = term254.
Proof. exact (TRANS (@lem5357249 _69726) (@lem5357250 _69726)). Qed.
Lemma lem5357252 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357253 (_69726 : int) : (term627 _69726) = term623.
Proof. exact (MK_COMB (@lem5357252) (@lem5357251 _69726)). Qed.
Lemma lem5357254 : term312 = term312.
Proof. exact (eq_refl term312). Qed.
Lemma lem5357255 (_69726 : int) : (term625 _69726) = term628.
Proof. exact (MK_COMB (@lem5357253 _69726) (@lem5357254)). Qed.
Lemma lem5357256 (_69726 : int) : (term668 _69726) = term628.
Proof. exact (TRANS (@lem5357145 _69726) (@lem5357255 _69726)). Qed.
Lemma lem5357257 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5357258 (_69726 : int) : (term668 _69726) = term312.
Proof. exact (TRANS (@lem5357256 _69726) (@lem5357257)). Qed.
Lemma lem5357259 (_69725 : int) (_69726 : int) : (term667 _69725 _69726) = term628.
Proof. exact (MK_COMB (@lem5357144 _69725) (@lem5357258 _69726)). Qed.
Lemma lem5357260 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = term628.
Proof. exact (TRANS (@lem5357036 _69725 _69726) (@lem5357259 _69725 _69726)). Qed.
Lemma lem5357261 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5357262 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = term312.
Proof. exact (TRANS (@lem5357260 _69725 _69726) (@lem5357261)). Qed.
Lemma lem5357263 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5357264 (_69725 : int) (_69726 : int) : (term669 _69725 _69726) = term630.
Proof. exact (MK_COMB (@lem5357263) (@lem5357262 _69725 _69726)). Qed.
Lemma lem5357265 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5357266 (_69725 : int) (_69726 : int) : (term665 _69725 _69726) = term631.
Proof. exact (MK_COMB (@lem5357264 _69725 _69726) (@lem5357265)). Qed.
Lemma lem5357267 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : term631.
Proof. exact (EQ_MP (@lem5357266 _69725 _69726) (@lem5357035 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357269 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5357270 : term631 = term632.
Proof. exact (@lem5357269 term254 term312). Qed.
Lemma lem5357272 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5357273 : term312 = term313.
Proof. exact (@lem5357272 term146). Qed.
Lemma lem5357275 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5357276 : term254 = term309.
Proof. exact (@lem5357275 (NUMERAL 0)). Qed.
Lemma lem5357277 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5357278 : term256 = term633.
Proof. exact (MK_COMB (@lem5357277) (@lem5357276)). Qed.
Lemma lem5357279 : term632 = term634.
Proof. exact (MK_COMB (@lem5357278) (@lem5357273)). Qed.
Lemma lem5357280 : term635.
Proof. exact (@lem1980026 term254 term267 term312 term267). Qed.
Lemma lem5357282 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357283 : term380 = term381.
Proof. exact (@lem5357282 (NUMERAL 0) term146). Qed.
Lemma lem5357284 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357285 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357286 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357285 h1) (fun h1 : term381 = True => @lem5357284)). Qed.
Lemma lem5357287 : term381 = True.
Proof. exact (EQ_MP (@lem5357286) (@lem5357284)). Qed.
Lemma lem5357288 : term380 = True.
Proof. exact (TRANS (@lem5357283) (@lem5357287)). Qed.
Lemma lem5357289 : True = term380.
Proof. exact (SYM (@lem5357288)). Qed.
Lemma lem5357290 : term380.
Proof. exact (EQ_MP (@lem5357289) (@lem0)). Qed.
Lemma lem5357291 : term636.
Proof. exact (@lem5357280 (@lem5357290)). Qed.
Lemma lem5357293 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357294 : term380 = term381.
Proof. exact (@lem5357293 (NUMERAL 0) term146). Qed.
Lemma lem5357295 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357296 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357297 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357296 h1) (fun h1 : term381 = True => @lem5357295)). Qed.
Lemma lem5357298 : term381 = True.
Proof. exact (EQ_MP (@lem5357297) (@lem5357295)). Qed.
Lemma lem5357299 : term380 = True.
Proof. exact (TRANS (@lem5357294) (@lem5357298)). Qed.
Lemma lem5357300 : True = term380.
Proof. exact (SYM (@lem5357299)). Qed.
Lemma lem5357301 : term380.
Proof. exact (EQ_MP (@lem5357300) (@lem0)). Qed.
Lemma lem5357302 : term634 = term637.
Proof. exact (@lem5357291 (@lem5357301)). Qed.
Lemma lem5357304 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5357305 : term347 = term352.
Proof. exact (@lem5357304 term146 term146). Qed.
Lemma lem5357306 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357307 : term324 = term146.
Proof. exact (EQ_MP (@lem5357306) (@lem940073)). Qed.
Lemma lem5357308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357309 : term322 = term267.
Proof. exact (MK_COMB (@lem5357308) (@lem5357307)). Qed.
Lemma lem5357310 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5357311 : term352 = term312.
Proof. exact (MK_COMB (@lem5357310) (@lem5357309)). Qed.
Lemma lem5357312 : term347 = term312.
Proof. exact (TRANS (@lem5357305) (@lem5357311)). Qed.
Lemma lem5357314 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357315 : term392 = term254.
Proof. exact (@lem5357314 term146). Qed.
Lemma lem5357316 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5357317 : term638 = term256.
Proof. exact (MK_COMB (@lem5357316) (@lem5357315)). Qed.
Lemma lem5357318 : term637 = term632.
Proof. exact (MK_COMB (@lem5357317) (@lem5357312)). Qed.
Lemma lem5357320 (m : nat) (n : nat) : (term639 m n) = (term640 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5357321 : term632 = term641.
Proof. exact (@lem5357320 (NUMERAL 0) term146). Qed.
Lemma lem5357322 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357323 (h1 : term382 = (BIT1 0)) : (term146 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5357324 : (term382 = (BIT1 0)) = ((term146 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357323 h1) (fun h1 : (term146 = (NUMERAL 0)) = False => @lem5357322)). Qed.
Lemma lem5357325 : (term146 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5357324) (@lem5357322)). Qed.
Lemma lem5357326 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5357327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5357328 : term642 = (and True).
Proof. exact (MK_COMB (@lem5357327) (@lem5357326)). Qed.
Lemma lem5357329 : term641 = (True /\ False).
Proof. exact (MK_COMB (@lem5357328) (@lem5357325)). Qed.
Lemma lem5357331 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5357332 : term641 = False.
Proof. exact (TRANS (@lem5357329) (@lem5357331)). Qed.
Lemma lem5357333 : term632 = False.
Proof. exact (TRANS (@lem5357321) (@lem5357332)). Qed.
Lemma lem5357334 : term637 = False.
Proof. exact (TRANS (@lem5357318) (@lem5357333)). Qed.
Lemma lem5357335 : term634 = False.
Proof. exact (TRANS (@lem5357302) (@lem5357334)). Qed.
Lemma lem5357336 : term632 = False.
Proof. exact (TRANS (@lem5357279) (@lem5357335)). Qed.
Lemma lem5357337 : term631 = False.
Proof. exact (TRANS (@lem5357270) (@lem5357336)). Qed.
Lemma lem5357338 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term723 _69724 _69725 _69726) : False.
Proof. exact (EQ_MP (@lem5357337) (@lem5357267 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357339 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term748 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5357340 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term555 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5357339 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357342 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term524 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5357340 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357344 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term493 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5357342 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357346 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term462 _69724 _69725 _69726.
Proof. exact (proj2 (@lem5357344 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357348 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term363 _69725 _69726.
Proof. exact (proj2 (@lem5357346 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357349 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term410 _69724 _69725 _69726.
Proof. exact (proj1 (@lem5357346 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357350 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term398 _69725 _69726.
Proof. exact (proj2 (@lem5357349 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357353 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5357354 : term580 = term380.
Proof. exact (@lem5357353 term254 term267). Qed.
Lemma lem5357356 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5357357 : term267 = term346.
Proof. exact (@lem5357356 term146). Qed.
Lemma lem5357359 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5357360 : term254 = term309.
Proof. exact (@lem5357359 (NUMERAL 0)). Qed.
Lemma lem5357361 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5357362 : term581 = term582.
Proof. exact (MK_COMB (@lem5357361) (@lem5357360)). Qed.
Lemma lem5357363 : term380 = term583.
Proof. exact (MK_COMB (@lem5357362) (@lem5357357)). Qed.
Lemma lem5357364 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5357366 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357367 : term380 = term381.
Proof. exact (@lem5357366 (NUMERAL 0) term146). Qed.
Lemma lem5357368 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357369 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357370 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357369 h1) (fun h1 : term381 = True => @lem5357368)). Qed.
Lemma lem5357371 : term381 = True.
Proof. exact (EQ_MP (@lem5357370) (@lem5357368)). Qed.
Lemma lem5357372 : term380 = True.
Proof. exact (TRANS (@lem5357367) (@lem5357371)). Qed.
Lemma lem5357373 : True = term380.
Proof. exact (SYM (@lem5357372)). Qed.
Lemma lem5357374 : term380.
Proof. exact (EQ_MP (@lem5357373) (@lem0)). Qed.
Lemma lem5357375 : term585.
Proof. exact (@lem5357364 (@lem5357374)). Qed.
Lemma lem5357377 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357378 : term380 = term381.
Proof. exact (@lem5357377 (NUMERAL 0) term146). Qed.
Lemma lem5357379 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357380 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357381 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357380 h1) (fun h1 : term381 = True => @lem5357379)). Qed.
Lemma lem5357382 : term381 = True.
Proof. exact (EQ_MP (@lem5357381) (@lem5357379)). Qed.
Lemma lem5357383 : term380 = True.
Proof. exact (TRANS (@lem5357378) (@lem5357382)). Qed.
Lemma lem5357384 : True = term380.
Proof. exact (SYM (@lem5357383)). Qed.
Lemma lem5357385 : term380.
Proof. exact (EQ_MP (@lem5357384) (@lem0)). Qed.
Lemma lem5357386 : term583 = term586.
Proof. exact (@lem5357375 (@lem5357385)). Qed.
Lemma lem5357388 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5357389 : term321 = term322.
Proof. exact (@lem5357388 term146 term146). Qed.
Lemma lem5357390 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357391 : term324 = term146.
Proof. exact (EQ_MP (@lem5357390) (@lem940073)). Qed.
Lemma lem5357392 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357393 : term322 = term267.
Proof. exact (MK_COMB (@lem5357392) (@lem5357391)). Qed.
Lemma lem5357394 : term321 = term267.
Proof. exact (TRANS (@lem5357389) (@lem5357393)). Qed.
Lemma lem5357396 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357397 : term392 = term254.
Proof. exact (@lem5357396 term146). Qed.
Lemma lem5357398 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5357399 : term587 = term581.
Proof. exact (MK_COMB (@lem5357398) (@lem5357397)). Qed.
Lemma lem5357400 : term586 = term380.
Proof. exact (MK_COMB (@lem5357399) (@lem5357394)). Qed.
Lemma lem5357402 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357403 : term380 = term381.
Proof. exact (@lem5357402 (NUMERAL 0) term146). Qed.
Lemma lem5357404 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357405 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357406 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357405 h1) (fun h1 : term381 = True => @lem5357404)). Qed.
Lemma lem5357407 : term381 = True.
Proof. exact (EQ_MP (@lem5357406) (@lem5357404)). Qed.
Lemma lem5357408 : term380 = True.
Proof. exact (TRANS (@lem5357403) (@lem5357407)). Qed.
Lemma lem5357409 : term586 = True.
Proof. exact (TRANS (@lem5357400) (@lem5357408)). Qed.
Lemma lem5357410 : term583 = True.
Proof. exact (TRANS (@lem5357386) (@lem5357409)). Qed.
Lemma lem5357411 : term380 = True.
Proof. exact (TRANS (@lem5357363) (@lem5357410)). Qed.
Lemma lem5357412 : term580 = True.
Proof. exact (TRANS (@lem5357354) (@lem5357411)). Qed.
Lemma lem5357413 : True = term580.
Proof. exact (SYM (@lem5357412)). Qed.
Lemma lem5357414 : term580.
Proof. exact (EQ_MP (@lem5357413) (@lem0)). Qed.
Lemma lem5357415 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term649 _69725 _69726.
Proof. exact (conj (@lem5357414) (@lem5357350 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357417 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5357418 (_69725 : int) (_69726 : int) : term650 _69725 _69726.
Proof. exact (@lem5357417 term267 (term335 _69725 _69726)). Qed.
Lemma lem5357419 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term651 _69725 _69726.
Proof. exact (@lem5357418 _69725 _69726 (@lem5357415 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357420 (_69725 : int) (_69726 : int) : (term652 _69725 _69726) = (term335 _69725 _69726).
Proof. exact (@lem1982733 (term335 _69725 _69726)). Qed.
Lemma lem5357421 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5357422 (_69725 : int) (_69726 : int) : (term653 _69725 _69726) = (term397 _69725 _69726).
Proof. exact (MK_COMB (@lem5357421) (@lem5357420 _69725 _69726)). Qed.
Lemma lem5357423 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5357424 (_69725 : int) (_69726 : int) : (term651 _69725 _69726) = (term398 _69725 _69726).
Proof. exact (MK_COMB (@lem5357422 _69725 _69726) (@lem5357423)). Qed.
Lemma lem5357425 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term398 _69725 _69726.
Proof. exact (EQ_MP (@lem5357424 _69725 _69726) (@lem5357419 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357427 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5357428 : term580 = term380.
Proof. exact (@lem5357427 term254 term267). Qed.
Lemma lem5357430 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5357431 : term267 = term346.
Proof. exact (@lem5357430 term146). Qed.
Lemma lem5357433 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5357434 : term254 = term309.
Proof. exact (@lem5357433 (NUMERAL 0)). Qed.
Lemma lem5357435 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5357436 : term581 = term582.
Proof. exact (MK_COMB (@lem5357435) (@lem5357434)). Qed.
Lemma lem5357437 : term380 = term583.
Proof. exact (MK_COMB (@lem5357436) (@lem5357431)). Qed.
Lemma lem5357438 : term584.
Proof. exact (@lem1980255 term254 term267 term267 term267). Qed.
Lemma lem5357440 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357441 : term380 = term381.
Proof. exact (@lem5357440 (NUMERAL 0) term146). Qed.
Lemma lem5357442 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357443 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357444 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357443 h1) (fun h1 : term381 = True => @lem5357442)). Qed.
Lemma lem5357445 : term381 = True.
Proof. exact (EQ_MP (@lem5357444) (@lem5357442)). Qed.
Lemma lem5357446 : term380 = True.
Proof. exact (TRANS (@lem5357441) (@lem5357445)). Qed.
Lemma lem5357447 : True = term380.
Proof. exact (SYM (@lem5357446)). Qed.
Lemma lem5357448 : term380.
Proof. exact (EQ_MP (@lem5357447) (@lem0)). Qed.
Lemma lem5357449 : term585.
Proof. exact (@lem5357438 (@lem5357448)). Qed.
Lemma lem5357451 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357452 : term380 = term381.
Proof. exact (@lem5357451 (NUMERAL 0) term146). Qed.
Lemma lem5357453 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357454 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357455 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357454 h1) (fun h1 : term381 = True => @lem5357453)). Qed.
Lemma lem5357456 : term381 = True.
Proof. exact (EQ_MP (@lem5357455) (@lem5357453)). Qed.
Lemma lem5357457 : term380 = True.
Proof. exact (TRANS (@lem5357452) (@lem5357456)). Qed.
Lemma lem5357458 : True = term380.
Proof. exact (SYM (@lem5357457)). Qed.
Lemma lem5357459 : term380.
Proof. exact (EQ_MP (@lem5357458) (@lem0)). Qed.
Lemma lem5357460 : term583 = term586.
Proof. exact (@lem5357449 (@lem5357459)). Qed.
Lemma lem5357462 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5357463 : term321 = term322.
Proof. exact (@lem5357462 term146 term146). Qed.
Lemma lem5357464 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357465 : term324 = term146.
Proof. exact (EQ_MP (@lem5357464) (@lem940073)). Qed.
Lemma lem5357466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357467 : term322 = term267.
Proof. exact (MK_COMB (@lem5357466) (@lem5357465)). Qed.
Lemma lem5357468 : term321 = term267.
Proof. exact (TRANS (@lem5357463) (@lem5357467)). Qed.
Lemma lem5357470 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357471 : term392 = term254.
Proof. exact (@lem5357470 term146). Qed.
Lemma lem5357472 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5357473 : term587 = term581.
Proof. exact (MK_COMB (@lem5357472) (@lem5357471)). Qed.
Lemma lem5357474 : term586 = term380.
Proof. exact (MK_COMB (@lem5357473) (@lem5357468)). Qed.
Lemma lem5357476 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357477 : term380 = term381.
Proof. exact (@lem5357476 (NUMERAL 0) term146). Qed.
Lemma lem5357478 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357479 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357480 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357479 h1) (fun h1 : term381 = True => @lem5357478)). Qed.
Lemma lem5357481 : term381 = True.
Proof. exact (EQ_MP (@lem5357480) (@lem5357478)). Qed.
Lemma lem5357482 : term380 = True.
Proof. exact (TRANS (@lem5357477) (@lem5357481)). Qed.
Lemma lem5357483 : term586 = True.
Proof. exact (TRANS (@lem5357474) (@lem5357482)). Qed.
Lemma lem5357484 : term583 = True.
Proof. exact (TRANS (@lem5357460) (@lem5357483)). Qed.
Lemma lem5357485 : term380 = True.
Proof. exact (TRANS (@lem5357437) (@lem5357484)). Qed.
Lemma lem5357486 : term580 = True.
Proof. exact (TRANS (@lem5357428) (@lem5357485)). Qed.
Lemma lem5357487 : True = term580.
Proof. exact (SYM (@lem5357486)). Qed.
Lemma lem5357488 : term580.
Proof. exact (EQ_MP (@lem5357487) (@lem0)). Qed.
Lemma lem5357489 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term644 _69725 _69726.
Proof. exact (conj (@lem5357488) (@lem5357348 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357491 (x : real) (y : real) : term589 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5357492 (_69725 : int) (_69726 : int) : term645 _69725 _69726.
Proof. exact (@lem5357491 term267 (term361 _69725 _69726)). Qed.
Lemma lem5357493 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term646 _69725 _69726.
Proof. exact (@lem5357492 _69725 _69726 (@lem5357489 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357494 (_69725 : int) (_69726 : int) : (term647 _69725 _69726) = (term361 _69725 _69726).
Proof. exact (@lem1982733 (term361 _69725 _69726)). Qed.
Lemma lem5357495 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5357496 (_69725 : int) (_69726 : int) : (term648 _69725 _69726) = (term362 _69725 _69726).
Proof. exact (MK_COMB (@lem5357495) (@lem5357494 _69725 _69726)). Qed.
Lemma lem5357497 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5357498 (_69725 : int) (_69726 : int) : (term646 _69725 _69726) = (term363 _69725 _69726).
Proof. exact (MK_COMB (@lem5357496 _69725 _69726) (@lem5357497)). Qed.
Lemma lem5357499 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term363 _69725 _69726.
Proof. exact (EQ_MP (@lem5357498 _69725 _69726) (@lem5357493 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357500 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term449 _69725 _69726.
Proof. exact (conj (@lem5357499 _69724 _69725 _69726 h1) (@lem5357425 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357502 (x : real) (y : real) : term600 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5357503 (_69725 : int) (_69726 : int) : term664 _69725 _69726.
Proof. exact (@lem5357502 (term361 _69725 _69726) (term335 _69725 _69726)). Qed.
Lemma lem5357504 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term665 _69725 _69726.
Proof. exact (@lem5357503 _69725 _69726 (@lem5357500 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357505 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = (term667 _69725 _69726).
Proof. exact (@lem1982753 (term337 _69725) (real_of_int _69725) (term659 _69726) (term337 _69726)). Qed.
Lemma lem5357506 (_69725 : int) : (term605 _69725) = (term606 _69725).
Proof. exact (@lem1982713 term312 (real_of_int _69725)). Qed.
Lemma lem5357508 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5357509 : term267 = term346.
Proof. exact (@lem5357508 term146). Qed.
Lemma lem5357511 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5357512 : term312 = term313.
Proof. exact (@lem5357511 term146). Qed.
Lemma lem5357513 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357514 : term607 = term608.
Proof. exact (MK_COMB (@lem5357513) (@lem5357512)). Qed.
Lemma lem5357515 : term609 = term610.
Proof. exact (MK_COMB (@lem5357514) (@lem5357509)). Qed.
Lemma lem5357516 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5357518 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357519 : term380 = term381.
Proof. exact (@lem5357518 (NUMERAL 0) term146). Qed.
Lemma lem5357520 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357521 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357522 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357521 h1) (fun h1 : term381 = True => @lem5357520)). Qed.
Lemma lem5357523 : term381 = True.
Proof. exact (EQ_MP (@lem5357522) (@lem5357520)). Qed.
Lemma lem5357524 : term380 = True.
Proof. exact (TRANS (@lem5357519) (@lem5357523)). Qed.
Lemma lem5357525 : True = term380.
Proof. exact (SYM (@lem5357524)). Qed.
Lemma lem5357526 : term380.
Proof. exact (EQ_MP (@lem5357525) (@lem0)). Qed.
Lemma lem5357527 : term612.
Proof. exact (@lem5357516 (@lem5357526)). Qed.
Lemma lem5357529 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357530 : term380 = term381.
Proof. exact (@lem5357529 (NUMERAL 0) term146). Qed.
Lemma lem5357531 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357532 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357533 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357532 h1) (fun h1 : term381 = True => @lem5357531)). Qed.
Lemma lem5357534 : term381 = True.
Proof. exact (EQ_MP (@lem5357533) (@lem5357531)). Qed.
Lemma lem5357535 : term380 = True.
Proof. exact (TRANS (@lem5357530) (@lem5357534)). Qed.
Lemma lem5357536 : True = term380.
Proof. exact (SYM (@lem5357535)). Qed.
Lemma lem5357537 : term380.
Proof. exact (EQ_MP (@lem5357536) (@lem0)). Qed.
Lemma lem5357538 : term613.
Proof. exact (@lem5357527 (@lem5357537)). Qed.
Lemma lem5357540 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357541 : term380 = term381.
Proof. exact (@lem5357540 (NUMERAL 0) term146). Qed.
Lemma lem5357542 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357543 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357544 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357543 h1) (fun h1 : term381 = True => @lem5357542)). Qed.
Lemma lem5357545 : term381 = True.
Proof. exact (EQ_MP (@lem5357544) (@lem5357542)). Qed.
Lemma lem5357546 : term380 = True.
Proof. exact (TRANS (@lem5357541) (@lem5357545)). Qed.
Lemma lem5357547 : True = term380.
Proof. exact (SYM (@lem5357546)). Qed.
Lemma lem5357548 : term380.
Proof. exact (EQ_MP (@lem5357547) (@lem0)). Qed.
Lemma lem5357549 : term614.
Proof. exact (@lem5357538 (@lem5357548)). Qed.
Lemma lem5357551 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5357552 : term321 = term322.
Proof. exact (@lem5357551 term146 term146). Qed.
Lemma lem5357553 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357554 : term324 = term146.
Proof. exact (EQ_MP (@lem5357553) (@lem940073)). Qed.
Lemma lem5357555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357556 : term322 = term267.
Proof. exact (MK_COMB (@lem5357555) (@lem5357554)). Qed.
Lemma lem5357557 : term321 = term267.
Proof. exact (TRANS (@lem5357552) (@lem5357556)). Qed.
Lemma lem5357559 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5357560 : term347 = term352.
Proof. exact (@lem5357559 term146 term146). Qed.
Lemma lem5357561 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357562 : term324 = term146.
Proof. exact (EQ_MP (@lem5357561) (@lem940073)). Qed.
Lemma lem5357563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357564 : term322 = term267.
Proof. exact (MK_COMB (@lem5357563) (@lem5357562)). Qed.
Lemma lem5357565 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5357566 : term352 = term312.
Proof. exact (MK_COMB (@lem5357565) (@lem5357564)). Qed.
Lemma lem5357567 : term347 = term312.
Proof. exact (TRANS (@lem5357560) (@lem5357566)). Qed.
Lemma lem5357568 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357569 : term615 = term607.
Proof. exact (MK_COMB (@lem5357568) (@lem5357567)). Qed.
Lemma lem5357570 : term616 = term609.
Proof. exact (MK_COMB (@lem5357569) (@lem5357557)). Qed.
Lemma lem5357572 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5357573 : term609 = term254.
Proof. exact (@lem5357572 term146). Qed.
Lemma lem5357574 : term616 = term254.
Proof. exact (TRANS (@lem5357570) (@lem5357573)). Qed.
Lemma lem5357575 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5357576 : term618 = term390.
Proof. exact (MK_COMB (@lem5357575) (@lem5357574)). Qed.
Lemma lem5357577 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5357578 : term619 = term392.
Proof. exact (MK_COMB (@lem5357576) (@lem5357577)). Qed.
Lemma lem5357580 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357581 : term392 = term254.
Proof. exact (@lem5357580 term146). Qed.
Lemma lem5357582 : term619 = term254.
Proof. exact (TRANS (@lem5357578) (@lem5357581)). Qed.
Lemma lem5357584 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5357585 : term321 = term322.
Proof. exact (@lem5357584 term146 term146). Qed.
Lemma lem5357586 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357587 : term324 = term146.
Proof. exact (EQ_MP (@lem5357586) (@lem940073)). Qed.
Lemma lem5357588 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357589 : term322 = term267.
Proof. exact (MK_COMB (@lem5357588) (@lem5357587)). Qed.
Lemma lem5357590 : term321 = term267.
Proof. exact (TRANS (@lem5357585) (@lem5357589)). Qed.
Lemma lem5357591 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5357592 : term394 = term392.
Proof. exact (MK_COMB (@lem5357591) (@lem5357590)). Qed.
Lemma lem5357594 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357595 : term392 = term254.
Proof. exact (@lem5357594 term146). Qed.
Lemma lem5357596 : term394 = term254.
Proof. exact (TRANS (@lem5357592) (@lem5357595)). Qed.
Lemma lem5357597 : term254 = term394.
Proof. exact (SYM (@lem5357596)). Qed.
Lemma lem5357598 : term619 = term394.
Proof. exact (TRANS (@lem5357582) (@lem5357597)). Qed.
Lemma lem5357599 : term610 = term309.
Proof. exact (@lem5357549 (@lem5357598)). Qed.
Lemma lem5357600 : term609 = term309.
Proof. exact (TRANS (@lem5357515) (@lem5357599)). Qed.
Lemma lem5357602 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5357603 : term309 = term254.
Proof. exact (@lem5357602 term254). Qed.
Lemma lem5357604 : term609 = term254.
Proof. exact (TRANS (@lem5357600) (@lem5357603)). Qed.
Lemma lem5357605 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5357606 : term620 = term390.
Proof. exact (MK_COMB (@lem5357605) (@lem5357604)). Qed.
Lemma lem5357607 (_69725 : int) : (real_of_int _69725) = (real_of_int _69725).
Proof. exact (eq_refl (real_of_int _69725)). Qed.
Lemma lem5357608 (_69725 : int) : (term606 _69725) = (term621 _69725).
Proof. exact (MK_COMB (@lem5357606) (@lem5357607 _69725)). Qed.
Lemma lem5357609 (_69725 : int) : (term605 _69725) = (term621 _69725).
Proof. exact (TRANS (@lem5357506 _69725) (@lem5357608 _69725)). Qed.
Lemma lem5357610 (_69725 : int) : (term621 _69725) = term254.
Proof. exact (@lem1982719 (real_of_int _69725)). Qed.
Lemma lem5357611 (_69725 : int) : (term605 _69725) = term254.
Proof. exact (TRANS (@lem5357609 _69725) (@lem5357610 _69725)). Qed.
Lemma lem5357612 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357613 (_69725 : int) : (term622 _69725) = term623.
Proof. exact (MK_COMB (@lem5357612) (@lem5357611 _69725)). Qed.
Lemma lem5357614 (_69726 : int) : (term668 _69726) = (term625 _69726).
Proof. exact (@lem1982759 (real_of_int _69726) (term337 _69726) term312). Qed.
Lemma lem5357615 (_69726 : int) : (term626 _69726) = (term606 _69726).
Proof. exact (@lem1982715 term312 (real_of_int _69726)). Qed.
Lemma lem5357617 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5357618 : term267 = term346.
Proof. exact (@lem5357617 term146). Qed.
Lemma lem5357620 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5357621 : term312 = term313.
Proof. exact (@lem5357620 term146). Qed.
Lemma lem5357622 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357623 : term607 = term608.
Proof. exact (MK_COMB (@lem5357622) (@lem5357621)). Qed.
Lemma lem5357624 : term609 = term610.
Proof. exact (MK_COMB (@lem5357623) (@lem5357618)). Qed.
Lemma lem5357625 : term611.
Proof. exact (@lem1981473 term312 term267 term267 term267 term254 term267). Qed.
Lemma lem5357627 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357628 : term380 = term381.
Proof. exact (@lem5357627 (NUMERAL 0) term146). Qed.
Lemma lem5357629 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357630 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357631 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357630 h1) (fun h1 : term381 = True => @lem5357629)). Qed.
Lemma lem5357632 : term381 = True.
Proof. exact (EQ_MP (@lem5357631) (@lem5357629)). Qed.
Lemma lem5357633 : term380 = True.
Proof. exact (TRANS (@lem5357628) (@lem5357632)). Qed.
Lemma lem5357634 : True = term380.
Proof. exact (SYM (@lem5357633)). Qed.
Lemma lem5357635 : term380.
Proof. exact (EQ_MP (@lem5357634) (@lem0)). Qed.
Lemma lem5357636 : term612.
Proof. exact (@lem5357625 (@lem5357635)). Qed.
Lemma lem5357638 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357639 : term380 = term381.
Proof. exact (@lem5357638 (NUMERAL 0) term146). Qed.
Lemma lem5357640 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357641 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357642 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357641 h1) (fun h1 : term381 = True => @lem5357640)). Qed.
Lemma lem5357643 : term381 = True.
Proof. exact (EQ_MP (@lem5357642) (@lem5357640)). Qed.
Lemma lem5357644 : term380 = True.
Proof. exact (TRANS (@lem5357639) (@lem5357643)). Qed.
Lemma lem5357645 : True = term380.
Proof. exact (SYM (@lem5357644)). Qed.
Lemma lem5357646 : term380.
Proof. exact (EQ_MP (@lem5357645) (@lem0)). Qed.
Lemma lem5357647 : term613.
Proof. exact (@lem5357636 (@lem5357646)). Qed.
Lemma lem5357649 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357650 : term380 = term381.
Proof. exact (@lem5357649 (NUMERAL 0) term146). Qed.
Lemma lem5357651 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357652 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357653 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357652 h1) (fun h1 : term381 = True => @lem5357651)). Qed.
Lemma lem5357654 : term381 = True.
Proof. exact (EQ_MP (@lem5357653) (@lem5357651)). Qed.
Lemma lem5357655 : term380 = True.
Proof. exact (TRANS (@lem5357650) (@lem5357654)). Qed.
Lemma lem5357656 : True = term380.
Proof. exact (SYM (@lem5357655)). Qed.
Lemma lem5357657 : term380.
Proof. exact (EQ_MP (@lem5357656) (@lem0)). Qed.
Lemma lem5357658 : term614.
Proof. exact (@lem5357647 (@lem5357657)). Qed.
Lemma lem5357660 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5357661 : term321 = term322.
Proof. exact (@lem5357660 term146 term146). Qed.
Lemma lem5357662 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357663 : term324 = term146.
Proof. exact (EQ_MP (@lem5357662) (@lem940073)). Qed.
Lemma lem5357664 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357665 : term322 = term267.
Proof. exact (MK_COMB (@lem5357664) (@lem5357663)). Qed.
Lemma lem5357666 : term321 = term267.
Proof. exact (TRANS (@lem5357661) (@lem5357665)). Qed.
Lemma lem5357668 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5357669 : term347 = term352.
Proof. exact (@lem5357668 term146 term146). Qed.
Lemma lem5357670 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357671 : term324 = term146.
Proof. exact (EQ_MP (@lem5357670) (@lem940073)). Qed.
Lemma lem5357672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357673 : term322 = term267.
Proof. exact (MK_COMB (@lem5357672) (@lem5357671)). Qed.
Lemma lem5357674 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5357675 : term352 = term312.
Proof. exact (MK_COMB (@lem5357674) (@lem5357673)). Qed.
Lemma lem5357676 : term347 = term312.
Proof. exact (TRANS (@lem5357669) (@lem5357675)). Qed.
Lemma lem5357677 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357678 : term615 = term607.
Proof. exact (MK_COMB (@lem5357677) (@lem5357676)). Qed.
Lemma lem5357679 : term616 = term609.
Proof. exact (MK_COMB (@lem5357678) (@lem5357666)). Qed.
Lemma lem5357681 (m : nat) : (term617 m) = term254.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5357682 : term609 = term254.
Proof. exact (@lem5357681 term146). Qed.
Lemma lem5357683 : term616 = term254.
Proof. exact (TRANS (@lem5357679) (@lem5357682)). Qed.
Lemma lem5357684 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5357685 : term618 = term390.
Proof. exact (MK_COMB (@lem5357684) (@lem5357683)). Qed.
Lemma lem5357686 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5357687 : term619 = term392.
Proof. exact (MK_COMB (@lem5357685) (@lem5357686)). Qed.
Lemma lem5357689 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357690 : term392 = term254.
Proof. exact (@lem5357689 term146). Qed.
Lemma lem5357691 : term619 = term254.
Proof. exact (TRANS (@lem5357687) (@lem5357690)). Qed.
Lemma lem5357693 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5357694 : term321 = term322.
Proof. exact (@lem5357693 term146 term146). Qed.
Lemma lem5357695 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357696 : term324 = term146.
Proof. exact (EQ_MP (@lem5357695) (@lem940073)). Qed.
Lemma lem5357697 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357698 : term322 = term267.
Proof. exact (MK_COMB (@lem5357697) (@lem5357696)). Qed.
Lemma lem5357699 : term321 = term267.
Proof. exact (TRANS (@lem5357694) (@lem5357698)). Qed.
Lemma lem5357700 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem5357701 : term394 = term392.
Proof. exact (MK_COMB (@lem5357700) (@lem5357699)). Qed.
Lemma lem5357703 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357704 : term392 = term254.
Proof. exact (@lem5357703 term146). Qed.
Lemma lem5357705 : term394 = term254.
Proof. exact (TRANS (@lem5357701) (@lem5357704)). Qed.
Lemma lem5357706 : term254 = term394.
Proof. exact (SYM (@lem5357705)). Qed.
Lemma lem5357707 : term619 = term394.
Proof. exact (TRANS (@lem5357691) (@lem5357706)). Qed.
Lemma lem5357708 : term610 = term309.
Proof. exact (@lem5357658 (@lem5357707)). Qed.
Lemma lem5357709 : term609 = term309.
Proof. exact (TRANS (@lem5357624) (@lem5357708)). Qed.
Lemma lem5357711 (x : real) : (term328 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5357712 : term309 = term254.
Proof. exact (@lem5357711 term254). Qed.
Lemma lem5357713 : term609 = term254.
Proof. exact (TRANS (@lem5357709) (@lem5357712)). Qed.
Lemma lem5357714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5357715 : term620 = term390.
Proof. exact (MK_COMB (@lem5357714) (@lem5357713)). Qed.
Lemma lem5357716 (_69726 : int) : (real_of_int _69726) = (real_of_int _69726).
Proof. exact (eq_refl (real_of_int _69726)). Qed.
Lemma lem5357717 (_69726 : int) : (term606 _69726) = (term621 _69726).
Proof. exact (MK_COMB (@lem5357715) (@lem5357716 _69726)). Qed.
Lemma lem5357718 (_69726 : int) : (term626 _69726) = (term621 _69726).
Proof. exact (TRANS (@lem5357615 _69726) (@lem5357717 _69726)). Qed.
Lemma lem5357719 (_69726 : int) : (term621 _69726) = term254.
Proof. exact (@lem1982719 (real_of_int _69726)). Qed.
Lemma lem5357720 (_69726 : int) : (term626 _69726) = term254.
Proof. exact (TRANS (@lem5357718 _69726) (@lem5357719 _69726)). Qed.
Lemma lem5357721 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5357722 (_69726 : int) : (term627 _69726) = term623.
Proof. exact (MK_COMB (@lem5357721) (@lem5357720 _69726)). Qed.
Lemma lem5357723 : term312 = term312.
Proof. exact (eq_refl term312). Qed.
Lemma lem5357724 (_69726 : int) : (term625 _69726) = term628.
Proof. exact (MK_COMB (@lem5357722 _69726) (@lem5357723)). Qed.
Lemma lem5357725 (_69726 : int) : (term668 _69726) = term628.
Proof. exact (TRANS (@lem5357614 _69726) (@lem5357724 _69726)). Qed.
Lemma lem5357726 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5357727 (_69726 : int) : (term668 _69726) = term312.
Proof. exact (TRANS (@lem5357725 _69726) (@lem5357726)). Qed.
Lemma lem5357728 (_69725 : int) (_69726 : int) : (term667 _69725 _69726) = term628.
Proof. exact (MK_COMB (@lem5357613 _69725) (@lem5357727 _69726)). Qed.
Lemma lem5357729 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = term628.
Proof. exact (TRANS (@lem5357505 _69725 _69726) (@lem5357728 _69725 _69726)). Qed.
Lemma lem5357730 : term628 = term312.
Proof. exact (@lem1982721 term312). Qed.
Lemma lem5357731 (_69725 : int) (_69726 : int) : (term666 _69725 _69726) = term312.
Proof. exact (TRANS (@lem5357729 _69725 _69726) (@lem5357730)). Qed.
Lemma lem5357732 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5357733 (_69725 : int) (_69726 : int) : (term669 _69725 _69726) = term630.
Proof. exact (MK_COMB (@lem5357732) (@lem5357731 _69725 _69726)). Qed.
Lemma lem5357734 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5357735 (_69725 : int) (_69726 : int) : (term665 _69725 _69726) = term631.
Proof. exact (MK_COMB (@lem5357733 _69725 _69726) (@lem5357734)). Qed.
Lemma lem5357736 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : term631.
Proof. exact (EQ_MP (@lem5357735 _69725 _69726) (@lem5357504 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357738 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5357739 : term631 = term632.
Proof. exact (@lem5357738 term254 term312). Qed.
Lemma lem5357741 (x : nat) : (term310 x) = (term311 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5357742 : term312 = term313.
Proof. exact (@lem5357741 term146). Qed.
Lemma lem5357744 (x : nat) : (real_of_num x) = (term308 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5357745 : term254 = term309.
Proof. exact (@lem5357744 (NUMERAL 0)). Qed.
Lemma lem5357746 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5357747 : term256 = term633.
Proof. exact (MK_COMB (@lem5357746) (@lem5357745)). Qed.
Lemma lem5357748 : term632 = term634.
Proof. exact (MK_COMB (@lem5357747) (@lem5357742)). Qed.
Lemma lem5357749 : term635.
Proof. exact (@lem1980026 term254 term267 term312 term267). Qed.
Lemma lem5357751 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357752 : term380 = term381.
Proof. exact (@lem5357751 (NUMERAL 0) term146). Qed.
Lemma lem5357753 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357754 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357755 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357754 h1) (fun h1 : term381 = True => @lem5357753)). Qed.
Lemma lem5357756 : term381 = True.
Proof. exact (EQ_MP (@lem5357755) (@lem5357753)). Qed.
Lemma lem5357757 : term380 = True.
Proof. exact (TRANS (@lem5357752) (@lem5357756)). Qed.
Lemma lem5357758 : True = term380.
Proof. exact (SYM (@lem5357757)). Qed.
Lemma lem5357759 : term380.
Proof. exact (EQ_MP (@lem5357758) (@lem0)). Qed.
Lemma lem5357760 : term636.
Proof. exact (@lem5357749 (@lem5357759)). Qed.
Lemma lem5357762 (m : nat) (n : nat) : (term379 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5357763 : term380 = term381.
Proof. exact (@lem5357762 (NUMERAL 0) term146). Qed.
Lemma lem5357764 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357765 (h1 : term382 = (BIT1 0)) : term381 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5357766 : (term382 = (BIT1 0)) = (term381 = True).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357765 h1) (fun h1 : term381 = True => @lem5357764)). Qed.
Lemma lem5357767 : term381 = True.
Proof. exact (EQ_MP (@lem5357766) (@lem5357764)). Qed.
Lemma lem5357768 : term380 = True.
Proof. exact (TRANS (@lem5357763) (@lem5357767)). Qed.
Lemma lem5357769 : True = term380.
Proof. exact (SYM (@lem5357768)). Qed.
Lemma lem5357770 : term380.
Proof. exact (EQ_MP (@lem5357769) (@lem0)). Qed.
Lemma lem5357771 : term634 = term637.
Proof. exact (@lem5357760 (@lem5357770)). Qed.
Lemma lem5357773 (m : nat) (n : nat) : (term350 m n) = (term351 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5357774 : term347 = term352.
Proof. exact (@lem5357773 term146 term146). Qed.
Lemma lem5357775 : (term323 = (BIT1 0)) = (term324 = term146).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5357776 : term324 = term146.
Proof. exact (EQ_MP (@lem5357775) (@lem940073)). Qed.
Lemma lem5357777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5357778 : term322 = term267.
Proof. exact (MK_COMB (@lem5357777) (@lem5357776)). Qed.
Lemma lem5357779 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5357780 : term352 = term312.
Proof. exact (MK_COMB (@lem5357779) (@lem5357778)). Qed.
Lemma lem5357781 : term347 = term312.
Proof. exact (TRANS (@lem5357774) (@lem5357780)). Qed.
Lemma lem5357783 (x : nat) : (term393 x) = term254.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5357784 : term392 = term254.
Proof. exact (@lem5357783 term146). Qed.
Lemma lem5357785 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5357786 : term638 = term256.
Proof. exact (MK_COMB (@lem5357785) (@lem5357784)). Qed.
Lemma lem5357787 : term637 = term632.
Proof. exact (MK_COMB (@lem5357786) (@lem5357781)). Qed.
Lemma lem5357789 (m : nat) (n : nat) : (term639 m n) = (term640 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5357790 : term632 = term641.
Proof. exact (@lem5357789 (NUMERAL 0) term146). Qed.
Lemma lem5357791 : term382 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5357792 (h1 : term382 = (BIT1 0)) : (term146 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5357793 : (term382 = (BIT1 0)) = ((term146 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term382 = (BIT1 0) => @lem5357792 h1) (fun h1 : (term146 = (NUMERAL 0)) = False => @lem5357791)). Qed.
Lemma lem5357794 : (term146 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5357793) (@lem5357791)). Qed.
Lemma lem5357795 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5357796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5357797 : term642 = (and True).
Proof. exact (MK_COMB (@lem5357796) (@lem5357795)). Qed.
Lemma lem5357798 : term641 = (True /\ False).
Proof. exact (MK_COMB (@lem5357797) (@lem5357794)). Qed.
Lemma lem5357800 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5357801 : term641 = False.
Proof. exact (TRANS (@lem5357798) (@lem5357800)). Qed.
Lemma lem5357802 : term632 = False.
Proof. exact (TRANS (@lem5357790) (@lem5357801)). Qed.
Lemma lem5357803 : term637 = False.
Proof. exact (TRANS (@lem5357787) (@lem5357802)). Qed.
Lemma lem5357804 : term634 = False.
Proof. exact (TRANS (@lem5357771) (@lem5357803)). Qed.
Lemma lem5357805 : term632 = False.
Proof. exact (TRANS (@lem5357748) (@lem5357804)). Qed.
Lemma lem5357806 : term631 = False.
Proof. exact (TRANS (@lem5357739) (@lem5357805)). Qed.
Lemma lem5357807 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term748 _69724 _69725 _69726) : False.
Proof. exact (EQ_MP (@lem5357806) (@lem5357736 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357808 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term553 _69724 _69725 _69726) : False.
Proof. exact (or_elim (@lem5356612 _69724 _69725 _69726 h1) (fun h0 : term723 _69724 _69725 _69726 => @lem5357338 _69724 _69725 _69726 h0) (fun h0 : term748 _69724 _69725 _69726 => @lem5357807 _69724 _69725 _69726 h0)). Qed.
Lemma lem5357809 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term562 _69724 _69725 _69726) : False.
Proof. exact (or_elim (@lem5355612 _69724 _69725 _69726 h1) (fun h0 : term557 _69725 _69724 _69726 => @lem5356611 _69725 _69724 _69726 h0) (fun h0 : term553 _69724 _69725 _69726 => @lem5357808 _69724 _69725 _69726 h0)). Qed.
Lemma lem5357810 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term578 _69724 _69725 _69726) : False.
Proof. exact (or_elim (@lem5353721 _69724 _69725 _69726 h1) (fun h0 : term575 _69724 _69725 _69726 => @lem5355611 _69724 _69725 _69726 h0) (fun h0 : term562 _69724 _69725 _69726 => @lem5357809 _69724 _69725 _69726 h0)). Qed.
Lemma lem5357812 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term578 _69724 _69725 _69726) : term578 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5357813 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term578 _69724 _69725 _69726) : (term578 _69724 _69725 _69726) = False.
Proof. exact (prop_ext (fun h2 : term578 _69724 _69725 _69726 => @lem5357810 _69724 _69725 _69726 h1) (fun h2 : False => @lem5357812 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357814 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term578 _69724 _69725 _69726) : False.
Proof. exact (EQ_MP (@lem5357813 _69724 _69725 _69726 h1) (@lem5357812 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357815 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term304 _69724 _69725 _69726) : term304 _69724 _69725 _69726.
Proof. exact (h1). Qed.
Lemma lem5357816 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term304 _69724 _69725 _69726) : term578 _69724 _69725 _69726.
Proof. exact (EQ_MP (@lem5353675 _69724 _69725 _69726) (@lem5357815 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357817 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term304 _69724 _69725 _69726) : (term578 _69724 _69725 _69726) = False.
Proof. exact (prop_ext (fun h2 : term578 _69724 _69725 _69726 => @lem5357814 _69724 _69725 _69726 h2) (fun h2 : False => @lem5357816 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357818 (_69724 : int) (_69725 : int) (_69726 : int) (h1 : term304 _69724 _69725 _69726) : False.
Proof. exact (EQ_MP (@lem5357817 _69724 _69725 _69726 h1) (@lem5357816 _69724 _69725 _69726 h1)). Qed.
Lemma lem5357819 (_69724 : int) (_69725 : int) (_69726 : int) : term749 _69724 _69725 _69726.
Proof. exact (fun h0 : term304 _69724 _69725 _69726 => @lem5357818 _69724 _69725 _69726 h0). Qed.
Lemma lem5357820 (_69724 : int) (_69725 : int) (_69726 : int) : term750 _69724 _69725 _69726.
Proof. exact (@lem1386578 (term751 _69724 _69725 _69726)). Qed.
Lemma lem5357823 (_69724 : int) (_69725 : int) (_69726 : int) : term751 _69724 _69725 _69726.
Proof. exact (@lem5357820 _69724 _69725 _69726 (@lem5357819 _69724 _69725 _69726)). Qed.
Lemma lem5357824 (_69724 : int) (_69726 : int) (_69725 : int) : (term302 _69724 _69725 _69726) = (term247 _69724 _69726 _69725).
Proof. exact (SYM (@lem5352341 _69724 _69725 _69726)). Qed.
Lemma lem5357825 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5357826 (_69724 : int) (_69726 : int) (_69725 : int) : (term751 _69724 _69725 _69726) = (term182 _69724 _69726 _69725).
Proof. exact (MK_COMB (@lem5357825) (@lem5357824 _69724 _69726 _69725)). Qed.
Lemma lem5357827 (_69724 : int) (_69726 : int) (_69725 : int) : term182 _69724 _69726 _69725.
Proof. exact (EQ_MP (@lem5357826 _69724 _69726 _69725) (@lem5357823 _69724 _69725 _69726)). Qed.
Lemma lem5357828 (_69724 : int) (_69726 : int) (_69725 : int) : term183 _69724 _69726 _69725.
Proof. exact (EQ_MP (@lem5351896 _69724 _69726 _69725) (@lem5357827 _69724 _69726 _69725)). Qed.
Lemma lem5357829 (m : nat) (x : nat) (n : nat) : term752 m x n.
Proof. exact (@lem5357828 (int_of_num m) (int_of_num x) (int_of_num n)). Qed.
Lemma lem5357830 (m : nat) (x : nat) (n : nat) : term753 m x n.
Proof. exact (@lem5357829 m x n (@lem5351889 m)). Qed.
Lemma lem5357831 (m : nat) (x : nat) (n : nat) : term754 m x n.
Proof. exact (@lem5357830 m x n (@lem5351892 n)). Qed.
Lemma lem5357832 (m : nat) (x : nat) (n : nat) : term173 m x n.
Proof. exact (@lem5357831 m x n (@lem5351895 x)). Qed.
Lemma lem5357833 (m : nat) (n : nat) : term175 m n.
Proof. exact (fun x : nat => @lem5357832 m x n). Qed.
Lemma lem5357834 (m : nat) : term177 m.
Proof. exact (fun n : nat => @lem5357833 m n). Qed.
Lemma lem5357835 : term179.
Proof. exact (fun m : nat => @lem5357834 m). Qed.
Lemma lem5357836 : term179 = term86.
Proof. exact (SYM (@lem5351886)). Qed.
Lemma lem5357837 : term86.
Proof. exact (EQ_MP (@lem5357836) (@lem5357835)). Qed.
Lemma lem5357838 : term86 = (term86 = True).
Proof. exact (@lem7 term86). Qed.
Lemma lem5357839 : term86 = True.
Proof. exact (EQ_MP (@lem5357838) (@lem5357837)). Qed.
Lemma lem5357840 : True = term86.
Proof. exact (SYM (@lem5357839)). Qed.
Lemma lem5357841 : term86.
Proof. exact (EQ_MP (@lem5357840) (@lem0)). Qed.
Lemma lem5357842 : term85.
Proof. exact (EQ_MP (@lem5351462) (@lem5357841)). Qed.
