Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_EXP_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import LE_ANTISYM_spec.
Require Import LE_EXP_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem149202 (m : nat) (n : nat) (h1 : (term0 n m) = (m = n)) : (term0 n m) = (m = n).
Proof. exact (h1). Qed.
Lemma lem149203 (m : nat) (n : nat) (h1 : (term0 n m) = (m = n)) : (m = n) = (term0 n m).
Proof. exact (SYM (@lem149202 m n h1)). Qed.
Lemma lem149204 (n : nat) (m : nat) (h1 : (m = n) = (term0 n m)) : (m = n) = (term0 n m).
Proof. exact (h1). Qed.
Lemma lem149205 (n : nat) (m : nat) (h1 : (m = n) = (term0 n m)) : (term0 n m) = (m = n).
Proof. exact (SYM (@lem149204 n m h1)). Qed.
Lemma lem149206 (n : nat) (m : nat) : ((term0 n m) = (m = n)) = ((m = n) = (term0 n m)).
Proof. exact (prop_ext (fun h1 : (term0 n m) = (m = n) => @lem149203 m n h1) (fun h1 : (m = n) = (term0 n m) => @lem149205 n m h1)). Qed.
Lemma lem149207 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem149206 n m)). Qed.
Lemma lem149208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem149209 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem149208) (@lem149207 m)). Qed.
Lemma lem149210 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem149209 m)). Qed.
Lemma lem149211 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem149212 : term7 = term8.
Proof. exact (MK_COMB (@lem149211) (@lem149210)). Qed.
Lemma lem149213 : term8.
Proof. exact (EQ_MP (@lem149212) (@lem92426)). Qed.
Lemma lem149214 (m : nat) : term9 m.
Proof. exact (@lem149213 m). Qed.
Lemma lem149215 (m : nat) : (term9 m) = (term4 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem149216 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem149215 m) (@lem149214 m)). Qed.
Lemma lem149217 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem149216 m n). Qed.
Lemma lem149218 (n : nat) (m : nat) : (term10 m n) = ((m = n) = (term0 n m)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem149222 (m : nat) (n : nat) (h1 : (term0 n m) = (m = n)) : (term0 n m) = (m = n).
Proof. exact (h1). Qed.
Lemma lem149223 (m : nat) (n : nat) (h1 : (term0 n m) = (m = n)) : (m = n) = (term0 n m).
Proof. exact (SYM (@lem149222 m n h1)). Qed.
Lemma lem149224 (n : nat) (m : nat) (h1 : (m = n) = (term0 n m)) : (m = n) = (term0 n m).
Proof. exact (h1). Qed.
Lemma lem149225 (n : nat) (m : nat) (h1 : (m = n) = (term0 n m)) : (term0 n m) = (m = n).
Proof. exact (SYM (@lem149224 n m h1)). Qed.
Lemma lem149226 (n : nat) (m : nat) : ((term0 n m) = (m = n)) = ((m = n) = (term0 n m)).
Proof. exact (prop_ext (fun h1 : (term0 n m) = (m = n) => @lem149223 m n h1) (fun h1 : (m = n) = (term0 n m) => @lem149225 n m h1)). Qed.
Lemma lem149227 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem149226 n m)). Qed.
Lemma lem149228 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem149229 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem149228) (@lem149227 m)). Qed.
Lemma lem149230 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem149229 m)). Qed.
Lemma lem149231 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem149232 : term7 = term8.
Proof. exact (MK_COMB (@lem149231) (@lem149230)). Qed.
Lemma lem149233 : term8.
Proof. exact (EQ_MP (@lem149232) (@lem92426)). Qed.
Lemma lem149243 (m : nat) : term9 m.
Proof. exact (@lem149233 m). Qed.
Lemma lem149244 (m : nat) : (term9 m) = (term4 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem149245 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem149244 m) (@lem149243 m)). Qed.
Lemma lem149246 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem149245 m n). Qed.
Lemma lem149247 (n : nat) (m : nat) : (term10 m n) = ((m = n) = (term0 n m)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem149250 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149247 n m) (@lem149246 m n)). Qed.
Lemma lem149251 (n : nat) (x : nat) (m : nat) : ((Nat.pow x m) = (Nat.pow x n)) = (term11 n x m).
Proof. exact (@lem149250 (Nat.pow x n) (Nat.pow x m)). Qed.
Lemma lem149252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149253 (n : nat) (x : nat) (m : nat) : (term12 m x n) = (term13 n x m).
Proof. exact (MK_COMB (@lem149252) (@lem149251 n x m)). Qed.
Lemma lem149254 (x : nat) (m : nat) (n : nat) : (term14 x m n) = (term14 x m n).
Proof. exact (eq_refl (term14 x m n)). Qed.
Lemma lem149255 (x : nat) (m : nat) (n : nat) : (((Nat.pow x m) = (Nat.pow x n)) = (term14 x m n)) = ((term11 n x m) = (term14 x m n)).
Proof. exact (MK_COMB (@lem149253 n x m) (@lem149254 x m n)). Qed.
Lemma lem149256 (x : nat) (m : nat) (n : nat) : ((term11 n x m) = (term14 x m n)) = (((Nat.pow x m) = (Nat.pow x n)) = (term14 x m n)).
Proof. exact (SYM (@lem149255 x m n)). Qed.
Lemma lem149257 (_474 : Prop) (_475 : Prop) (_476 : Prop -> Prop) (_477 : Prop) : (term15 _476 _475 _474 _477) = (term16 _474 _475 _476 _477).
Proof. exact (@lem13473 Prop _474 _475 _476 _477). Qed.
Lemma lem149258 (_474 : Prop) (_475 : Prop) (n : nat) (x : nat) (m : nat) (_477 : Prop) : (term17 n x m _475 _474 _477) = (term18 _474 _475 n x m _477).
Proof. exact (@lem149257 _474 _475 (term19 n x m) _477). Qed.
Lemma lem149259 (x : nat) (m : nat) (n : nat) : (term20 x m n) = (term21 x m n).
Proof. exact (@lem149258 ((m = (NUMERAL 0)) = (n = (NUMERAL 0))) (x = (NUMERAL 0)) n x m (term22 x m n)). Qed.
Lemma lem149260 (x : nat) (m : nat) (n : nat) : (term23 x m n) = ((term11 n x m) = (term22 x m n)).
Proof. exact (eq_refl (term23 x m n)). Qed.
Lemma lem149261 (x : nat) : (term24 x) = (term24 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem149262 (x : nat) (m : nat) (n : nat) : (term25 x m n) = (term26 x m n).
Proof. exact (MK_COMB (@lem149261 x) (@lem149260 x m n)). Qed.
Lemma lem149263 (x : nat) (m : nat) (n : nat) : (term27 x m n) = ((term11 n x m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0)))).
Proof. exact (eq_refl (term27 x m n)). Qed.
Lemma lem149264 (x : nat) : (term28 x) = (term28 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem149265 (x : nat) (m : nat) (n : nat) : (term29 x m n) = (term30 x m n).
Proof. exact (MK_COMB (@lem149264 x) (@lem149263 x m n)). Qed.
Lemma lem149266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem149267 (x : nat) (m : nat) (n : nat) : (term31 x m n) = (term32 x m n).
Proof. exact (MK_COMB (@lem149266) (@lem149265 x m n)). Qed.
Lemma lem149268 (x : nat) (m : nat) (n : nat) : (term21 x m n) = (term33 x m n).
Proof. exact (MK_COMB (@lem149267 x m n) (@lem149262 x m n)). Qed.
Lemma lem149269 (x : nat) (m : nat) (n : nat) : (term20 x m n) = ((term11 n x m) = (term14 x m n)).
Proof. exact (eq_refl (term20 x m n)). Qed.
Lemma lem149270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149271 (x : nat) (m : nat) (n : nat) : (term34 x m n) = (term35 x m n).
Proof. exact (MK_COMB (@lem149270) (@lem149269 x m n)). Qed.
Lemma lem149272 (x : nat) (m : nat) (n : nat) : ((term20 x m n) = (term21 x m n)) = (((term11 n x m) = (term14 x m n)) = (term33 x m n)).
Proof. exact (MK_COMB (@lem149271 x m n) (@lem149268 x m n)). Qed.
Lemma lem149273 (x : nat) (m : nat) (n : nat) : ((term11 n x m) = (term14 x m n)) = (term33 x m n).
Proof. exact (EQ_MP (@lem149272 x m n) (@lem149259 x m n)). Qed.
Lemma lem149274 (x : nat) (m : nat) (n : nat) : (term33 x m n) = ((term11 n x m) = (term14 x m n)).
Proof. exact (SYM (@lem149273 x m n)). Qed.
Lemma lem149275 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem149292 (x : nat) (h1 : term36 x) : term36 x.
Proof. exact (h1). Qed.
Lemma lem149309 (x : nat) : term37 x.
Proof. exact (@lem149199 x). Qed.
Lemma lem149310 (x : nat) : (term37 x) = (term38 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem149311 (x : nat) : term38 x.
Proof. exact (EQ_MP (@lem149310 x) (@lem149309 x)). Qed.
Lemma lem149312 (x : nat) (m : nat) : term39 x m.
Proof. exact (@lem149311 x m). Qed.
Lemma lem149313 (x : nat) (m : nat) : (term39 x m) = (term40 x m).
Proof. exact (eq_refl (term39 x m)). Qed.
Lemma lem149314 (x : nat) (m : nat) : term40 x m.
Proof. exact (EQ_MP (@lem149313 x m) (@lem149312 x m)). Qed.
Lemma lem149315 (x : nat) (m : nat) (n : nat) : term41 x m n.
Proof. exact (@lem149314 x m n). Qed.
Lemma lem149316 (x : nat) (m : nat) (n : nat) : (term41 x m n) = ((term42 m x n) = (term43 x m n)).
Proof. exact (eq_refl (term41 x m n)). Qed.
Lemma lem149323 (x : nat) (m : nat) (n : nat) : (term42 m x n) = (term43 x m n).
Proof. exact (EQ_MP (@lem149316 x m n) (@lem149315 x m n)). Qed.
Lemma lem149329 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem149330 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem149331 (x : nat) (h1 : x = (NUMERAL 0)) : (@eq nat x) = term44.
Proof. exact (MK_COMB (@lem149330) (@lem149329 x h1)). Qed.
Lemma lem149332 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem149333 (x : nat) (h1 : x = (NUMERAL 0)) : (x = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem149331 x h1) (@lem149332)). Qed.
Lemma lem149335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem149336 (x : nat) : (x = x) = True.
Proof. exact (@lem149335 nat x). Qed.
Lemma lem149337 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem149336 (NUMERAL 0)). Qed.
Lemma lem149338 (x : nat) (h1 : x = (NUMERAL 0)) : (x = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem149333 x h1) (@lem149337)). Qed.
Lemma lem149339 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem149340 (x : nat) (h1 : x = (NUMERAL 0)) : (term45 x) = (@COND Prop True).
Proof. exact (MK_COMB (@lem149339) (@lem149338 x h1)). Qed.
Lemma lem149349 (m : nat) (n : nat) : (term46 m n) = (term46 m n).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem149350 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term47 x m n) = (term48 m n).
Proof. exact (MK_COMB (@lem149340 x h1) (@lem149349 m n)). Qed.
Lemma lem149356 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem149357 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem149358 (x : nat) (h1 : x = (NUMERAL 0)) : (@eq nat x) = term44.
Proof. exact (MK_COMB (@lem149357) (@lem149356 x h1)). Qed.
Lemma lem149359 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem149360 (x : nat) (h1 : x = (NUMERAL 0)) : (x = term49) = ((NUMERAL 0) = term49).
Proof. exact (MK_COMB (@lem149358 x h1) (@lem149359)). Qed.
Lemma lem149363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem149364 (x : nat) (h1 : x = (NUMERAL 0)) : (term50 x) = term51.
Proof. exact (MK_COMB (@lem149363) (@lem149360 x h1)). Qed.
Lemma lem149365 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem149366 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term52 x m n) = (term53 m n).
Proof. exact (MK_COMB (@lem149364 x h1) (@lem149365 m n)). Qed.
Lemma lem149369 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term43 x m n) = (term54 m n).
Proof. exact (MK_COMB (@lem149350 m n x h1) (@lem149366 m n x h1)). Qed.
Lemma lem149371 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem149372 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem149371 Prop t2 t1). Qed.
Lemma lem149373 (m : nat) (n : nat) : (term54 m n) = (term46 m n).
Proof. exact (@lem149372 (term53 m n) (term46 m n)). Qed.
Lemma lem149382 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term43 x m n) = (term46 m n).
Proof. exact (TRANS (@lem149369 m n x h1) (@lem149373 m n)). Qed.
Lemma lem149383 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term42 m x n) = (term46 m n).
Proof. exact (TRANS (@lem149323 x m n) (@lem149382 m n x h1)). Qed.
Lemma lem149384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem149385 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term55 m x n) = (term56 m n).
Proof. exact (MK_COMB (@lem149384) (@lem149383 m n x h1)). Qed.
Lemma lem149387 (x : nat) (m : nat) (n : nat) : (term42 m x n) = (term43 x m n).
Proof. exact (EQ_MP (@lem149316 x m n) (@lem149315 x m n)). Qed.
Lemma lem149388 (x : nat) (n : nat) (m : nat) : (term42 n x m) = (term43 x n m).
Proof. exact (@lem149387 x n m). Qed.
Lemma lem149394 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem149395 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem149396 (x : nat) (h1 : x = (NUMERAL 0)) : (@eq nat x) = term44.
Proof. exact (MK_COMB (@lem149395) (@lem149394 x h1)). Qed.
Lemma lem149397 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem149398 (x : nat) (h1 : x = (NUMERAL 0)) : (x = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem149396 x h1) (@lem149397)). Qed.
Lemma lem149400 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem149401 (x : nat) : (x = x) = True.
Proof. exact (@lem149400 nat x). Qed.
Lemma lem149402 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem149401 (NUMERAL 0)). Qed.
Lemma lem149403 (x : nat) (h1 : x = (NUMERAL 0)) : (x = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem149398 x h1) (@lem149402)). Qed.
Lemma lem149404 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem149405 (x : nat) (h1 : x = (NUMERAL 0)) : (term45 x) = (@COND Prop True).
Proof. exact (MK_COMB (@lem149404) (@lem149403 x h1)). Qed.
Lemma lem149414 (n : nat) (m : nat) : (term46 n m) = (term46 n m).
Proof. exact (eq_refl (term46 n m)). Qed.
Lemma lem149415 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term47 x n m) = (term48 n m).
Proof. exact (MK_COMB (@lem149405 x h1) (@lem149414 n m)). Qed.
Lemma lem149421 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem149422 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem149423 (x : nat) (h1 : x = (NUMERAL 0)) : (@eq nat x) = term44.
Proof. exact (MK_COMB (@lem149422) (@lem149421 x h1)). Qed.
Lemma lem149424 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem149425 (x : nat) (h1 : x = (NUMERAL 0)) : (x = term49) = ((NUMERAL 0) = term49).
Proof. exact (MK_COMB (@lem149423 x h1) (@lem149424)). Qed.
Lemma lem149428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem149429 (x : nat) (h1 : x = (NUMERAL 0)) : (term50 x) = term51.
Proof. exact (MK_COMB (@lem149428) (@lem149425 x h1)). Qed.
Lemma lem149430 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem149431 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term52 x n m) = (term53 n m).
Proof. exact (MK_COMB (@lem149429 x h1) (@lem149430 n m)). Qed.
Lemma lem149434 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term43 x n m) = (term54 n m).
Proof. exact (MK_COMB (@lem149415 n m x h1) (@lem149431 n m x h1)). Qed.
Lemma lem149436 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem149437 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem149436 Prop t2 t1). Qed.
Lemma lem149438 (n : nat) (m : nat) : (term54 n m) = (term46 n m).
Proof. exact (@lem149437 (term53 n m) (term46 n m)). Qed.
Lemma lem149447 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term43 x n m) = (term46 n m).
Proof. exact (TRANS (@lem149434 n m x h1) (@lem149438 n m)). Qed.
Lemma lem149448 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term42 n x m) = (term46 n m).
Proof. exact (TRANS (@lem149388 x n m) (@lem149447 n m x h1)). Qed.
Lemma lem149449 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term11 n x m) = (term57 n m).
Proof. exact (MK_COMB (@lem149385 m n x h1) (@lem149448 n m x h1)). Qed.
Lemma lem149452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149453 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term13 n x m) = (term58 n m).
Proof. exact (MK_COMB (@lem149452) (@lem149449 n m x h1)). Qed.
Lemma lem149460 (m : nat) (n : nat) : ((m = (NUMERAL 0)) = (n = (NUMERAL 0))) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl ((m = (NUMERAL 0)) = (n = (NUMERAL 0)))). Qed.
Lemma lem149461 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : ((term11 n x m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0)))) = ((term57 n m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0)))).
Proof. exact (MK_COMB (@lem149453 n m x h1) (@lem149460 m n)). Qed.
Lemma lem149464 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : ((term57 n m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0)))) = ((term11 n x m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0)))).
Proof. exact (SYM (@lem149461 m n x h1)). Qed.
Lemma lem149465 (x : nat) : term37 x.
Proof. exact (@lem149199 x). Qed.
Lemma lem149466 (x : nat) : (term37 x) = (term38 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem149467 (x : nat) : term38 x.
Proof. exact (EQ_MP (@lem149466 x) (@lem149465 x)). Qed.
Lemma lem149468 (x : nat) (m : nat) : term39 x m.
Proof. exact (@lem149467 x m). Qed.
Lemma lem149469 (x : nat) (m : nat) : (term39 x m) = (term40 x m).
Proof. exact (eq_refl (term39 x m)). Qed.
Lemma lem149470 (x : nat) (m : nat) : term40 x m.
Proof. exact (EQ_MP (@lem149469 x m) (@lem149468 x m)). Qed.
Lemma lem149471 (x : nat) (m : nat) (n : nat) : term41 x m n.
Proof. exact (@lem149470 x m n). Qed.
Lemma lem149472 (x : nat) (m : nat) (n : nat) : (term41 x m n) = ((term42 m x n) = (term43 x m n)).
Proof. exact (eq_refl (term41 x m n)). Qed.
Lemma lem149474 (x : nat) : term59 x.
Proof. exact (@lem82 (x = (NUMERAL 0))). Qed.
Lemma lem149492 (x : nat) (m : nat) (n : nat) : (term42 m x n) = (term43 x m n).
Proof. exact (EQ_MP (@lem149472 x m n) (@lem149471 x m n)). Qed.
Lemma lem149496 (x : nat) (h1 : term36 x) : (x = (NUMERAL 0)) = False.
Proof. exact (@lem149474 x (@lem149292 x h1)). Qed.
Lemma lem149497 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem149498 (x : nat) (h1 : term36 x) : (term45 x) = (@COND Prop False).
Proof. exact (MK_COMB (@lem149497) (@lem149496 x h1)). Qed.
Lemma lem149507 (m : nat) (n : nat) : (term46 m n) = (term46 m n).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem149508 (m : nat) (n : nat) (x : nat) (h1 : term36 x) : (term47 x m n) = (term60 m n).
Proof. exact (MK_COMB (@lem149498 x h1) (@lem149507 m n)). Qed.
Lemma lem149513 (x : nat) (m : nat) (n : nat) : (term52 x m n) = (term52 x m n).
Proof. exact (eq_refl (term52 x m n)). Qed.
Lemma lem149514 (m : nat) (n : nat) (x : nat) (h1 : term36 x) : (term43 x m n) = (term61 x m n).
Proof. exact (MK_COMB (@lem149508 m n x h1) (@lem149513 x m n)). Qed.
Lemma lem149516 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem149517 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem149516 Prop t1 t2). Qed.
Lemma lem149518 (x : nat) (m : nat) (n : nat) : (term61 x m n) = (term52 x m n).
Proof. exact (@lem149517 (term46 m n) (term52 x m n)). Qed.
Lemma lem149523 (m : nat) (n : nat) (x : nat) (h1 : term36 x) : (term43 x m n) = (term52 x m n).
Proof. exact (TRANS (@lem149514 m n x h1) (@lem149518 x m n)). Qed.
Lemma lem149524 (m : nat) (n : nat) (x : nat) (h1 : term36 x) : (term42 m x n) = (term52 x m n).
Proof. exact (TRANS (@lem149492 x m n) (@lem149523 m n x h1)). Qed.
Lemma lem149525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem149526 (m : nat) (n : nat) (x : nat) (h1 : term36 x) : (term55 m x n) = (term62 x m n).
Proof. exact (MK_COMB (@lem149525) (@lem149524 m n x h1)). Qed.
Lemma lem149528 (x : nat) (m : nat) (n : nat) : (term42 m x n) = (term43 x m n).
Proof. exact (EQ_MP (@lem149472 x m n) (@lem149471 x m n)). Qed.
Lemma lem149529 (x : nat) (n : nat) (m : nat) : (term42 n x m) = (term43 x n m).
Proof. exact (@lem149528 x n m). Qed.
Lemma lem149533 (x : nat) (h1 : term36 x) : (x = (NUMERAL 0)) = False.
Proof. exact (@lem149474 x (@lem149292 x h1)). Qed.
Lemma lem149534 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem149535 (x : nat) (h1 : term36 x) : (term45 x) = (@COND Prop False).
Proof. exact (MK_COMB (@lem149534) (@lem149533 x h1)). Qed.
Lemma lem149544 (n : nat) (m : nat) : (term46 n m) = (term46 n m).
Proof. exact (eq_refl (term46 n m)). Qed.
Lemma lem149545 (n : nat) (m : nat) (x : nat) (h1 : term36 x) : (term47 x n m) = (term60 n m).
Proof. exact (MK_COMB (@lem149535 x h1) (@lem149544 n m)). Qed.
Lemma lem149550 (x : nat) (n : nat) (m : nat) : (term52 x n m) = (term52 x n m).
Proof. exact (eq_refl (term52 x n m)). Qed.
Lemma lem149551 (n : nat) (m : nat) (x : nat) (h1 : term36 x) : (term43 x n m) = (term61 x n m).
Proof. exact (MK_COMB (@lem149545 n m x h1) (@lem149550 x n m)). Qed.
Lemma lem149553 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem149554 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem149553 Prop t1 t2). Qed.
Lemma lem149555 (x : nat) (n : nat) (m : nat) : (term61 x n m) = (term52 x n m).
Proof. exact (@lem149554 (term46 n m) (term52 x n m)). Qed.
Lemma lem149560 (n : nat) (m : nat) (x : nat) (h1 : term36 x) : (term43 x n m) = (term52 x n m).
Proof. exact (TRANS (@lem149551 n m x h1) (@lem149555 x n m)). Qed.
Lemma lem149561 (n : nat) (m : nat) (x : nat) (h1 : term36 x) : (term42 n x m) = (term52 x n m).
Proof. exact (TRANS (@lem149529 x n m) (@lem149560 n m x h1)). Qed.
Lemma lem149562 (n : nat) (m : nat) (x : nat) (h1 : term36 x) : (term11 n x m) = (term63 x n m).
Proof. exact (MK_COMB (@lem149526 m n x h1) (@lem149561 n m x h1)). Qed.
Lemma lem149565 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149566 (n : nat) (m : nat) (x : nat) (h1 : term36 x) : (term13 n x m) = (term64 x n m).
Proof. exact (MK_COMB (@lem149565) (@lem149562 n m x h1)). Qed.
Lemma lem149573 (x : nat) (m : nat) (n : nat) : (term22 x m n) = (term22 x m n).
Proof. exact (eq_refl (term22 x m n)). Qed.
Lemma lem149574 (m : nat) (n : nat) (x : nat) (h1 : term36 x) : ((term11 n x m) = (term22 x m n)) = ((term63 x n m) = (term22 x m n)).
Proof. exact (MK_COMB (@lem149566 n m x h1) (@lem149573 x m n)). Qed.
Lemma lem149577 (m : nat) (n : nat) (x : nat) (h1 : term36 x) : ((term63 x n m) = (term22 x m n)) = ((term11 n x m) = (term22 x m n)).
Proof. exact (SYM (@lem149574 m n x h1)). Qed.
Lemma lem149591 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149218 n m) (@lem149217 m n)). Qed.
Lemma lem149592 (m : nat) : (m = (NUMERAL 0)) = (term65 m).
Proof. exact (@lem149591 (NUMERAL 0) m). Qed.
Lemma lem149595 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem149596 (m : nat) : (term28 m) = (term66 m).
Proof. exact (MK_COMB (@lem149595) (@lem149592 m)). Qed.
Lemma lem149600 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149218 n m) (@lem149217 m n)). Qed.
Lemma lem149601 (n : nat) : (n = (NUMERAL 0)) = (term65 n).
Proof. exact (@lem149600 (NUMERAL 0) n). Qed.
Lemma lem149604 (m : nat) (n : nat) : (term46 m n) = (term67 m n).
Proof. exact (MK_COMB (@lem149596 m) (@lem149601 n)). Qed.
Lemma lem149607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem149608 (m : nat) (n : nat) : (term56 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem149607) (@lem149604 m n)). Qed.
Lemma lem149616 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149218 n m) (@lem149217 m n)). Qed.
Lemma lem149617 (n : nat) : (n = (NUMERAL 0)) = (term65 n).
Proof. exact (@lem149616 (NUMERAL 0) n). Qed.
Lemma lem149620 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem149621 (n : nat) : (term28 n) = (term66 n).
Proof. exact (MK_COMB (@lem149620) (@lem149617 n)). Qed.
Lemma lem149625 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149218 n m) (@lem149217 m n)). Qed.
Lemma lem149626 (m : nat) : (m = (NUMERAL 0)) = (term65 m).
Proof. exact (@lem149625 (NUMERAL 0) m). Qed.
Lemma lem149629 (n : nat) (m : nat) : (term46 n m) = (term67 n m).
Proof. exact (MK_COMB (@lem149621 n) (@lem149626 m)). Qed.
Lemma lem149632 (n : nat) (m : nat) : (term57 n m) = (term69 n m).
Proof. exact (MK_COMB (@lem149608 m n) (@lem149629 n m)). Qed.
Lemma lem149635 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149636 (n : nat) (m : nat) : (term58 n m) = (term70 n m).
Proof. exact (MK_COMB (@lem149635) (@lem149632 n m)). Qed.
Lemma lem149644 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149218 n m) (@lem149217 m n)). Qed.
Lemma lem149645 (m : nat) : (m = (NUMERAL 0)) = (term65 m).
Proof. exact (@lem149644 (NUMERAL 0) m). Qed.
Lemma lem149648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149649 (m : nat) : (term71 m) = (term72 m).
Proof. exact (MK_COMB (@lem149648) (@lem149645 m)). Qed.
Lemma lem149653 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149218 n m) (@lem149217 m n)). Qed.
Lemma lem149654 (n : nat) : (n = (NUMERAL 0)) = (term65 n).
Proof. exact (@lem149653 (NUMERAL 0) n). Qed.
Lemma lem149657 (m : nat) (n : nat) : ((m = (NUMERAL 0)) = (n = (NUMERAL 0))) = ((term65 m) = (term65 n)).
Proof. exact (MK_COMB (@lem149649 m) (@lem149654 n)). Qed.
Lemma lem149662 (m : nat) (n : nat) : ((term57 n m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0)))) = ((term69 n m) = ((term65 m) = (term65 n))).
Proof. exact (MK_COMB (@lem149636 n m) (@lem149657 m n)). Qed.
Lemma lem149667 (m : nat) (n : nat) : ((term69 n m) = ((term65 m) = (term65 n))) = ((term57 n m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0)))).
Proof. exact (SYM (@lem149662 m n)). Qed.
Lemma lem149679 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149218 n m) (@lem149217 m n)). Qed.
Lemma lem149680 (x : nat) : (x = term49) = (term73 x).
Proof. exact (@lem149679 term49 x). Qed.
Lemma lem149683 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem149684 (x : nat) : (term50 x) = (term74 x).
Proof. exact (MK_COMB (@lem149683) (@lem149680 x)). Qed.
Lemma lem149685 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem149686 (x : nat) (m : nat) (n : nat) : (term52 x m n) = (term75 x m n).
Proof. exact (MK_COMB (@lem149684 x) (@lem149685 m n)). Qed.
Lemma lem149689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem149690 (x : nat) (m : nat) (n : nat) : (term62 x m n) = (term76 x m n).
Proof. exact (MK_COMB (@lem149689) (@lem149686 x m n)). Qed.
Lemma lem149696 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149218 n m) (@lem149217 m n)). Qed.
Lemma lem149697 (x : nat) : (x = term49) = (term73 x).
Proof. exact (@lem149696 term49 x). Qed.
Lemma lem149700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem149701 (x : nat) : (term50 x) = (term74 x).
Proof. exact (MK_COMB (@lem149700) (@lem149697 x)). Qed.
Lemma lem149702 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem149703 (x : nat) (n : nat) (m : nat) : (term52 x n m) = (term75 x n m).
Proof. exact (MK_COMB (@lem149701 x) (@lem149702 n m)). Qed.
Lemma lem149706 (x : nat) (n : nat) (m : nat) : (term63 x n m) = (term77 x n m).
Proof. exact (MK_COMB (@lem149690 x m n) (@lem149703 x n m)). Qed.
Lemma lem149709 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149710 (x : nat) (n : nat) (m : nat) : (term64 x n m) = (term78 x n m).
Proof. exact (MK_COMB (@lem149709) (@lem149706 x n m)). Qed.
Lemma lem149716 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149218 n m) (@lem149217 m n)). Qed.
Lemma lem149717 (x : nat) : (x = term49) = (term73 x).
Proof. exact (@lem149716 term49 x). Qed.
Lemma lem149720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem149721 (x : nat) : (term50 x) = (term74 x).
Proof. exact (MK_COMB (@lem149720) (@lem149717 x)). Qed.
Lemma lem149725 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem149218 n m) (@lem149217 m n)). Qed.
Lemma lem149728 (x : nat) (n : nat) (m : nat) : (term22 x m n) = (term79 x n m).
Proof. exact (MK_COMB (@lem149721 x) (@lem149725 n m)). Qed.
Lemma lem149731 (x : nat) (n : nat) (m : nat) : ((term63 x n m) = (term22 x m n)) = ((term77 x n m) = (term79 x n m)).
Proof. exact (MK_COMB (@lem149710 x n m) (@lem149728 x n m)). Qed.
Lemma lem149736 (x : nat) (m : nat) (n : nat) : ((term77 x n m) = (term79 x n m)) = ((term63 x n m) = (term22 x m n)).
Proof. exact (SYM (@lem149731 x n m)). Qed.
Lemma lem149761 (m : nat) : term80 m.
Proof. exact (@lem9851 (term81 m)). Qed.
Lemma lem149762 (m : nat) : (term80 m) = (term82 m).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem149763 (m : nat) : term82 m.
Proof. exact (EQ_MP (@lem149762 m) (@lem149761 m)). Qed.
Lemma lem149764 (m : nat) (h1 : (term81 m) = True) : (term81 m) = True.
Proof. exact (h1). Qed.
Lemma lem149765 (m : nat) (h1 : (term81 m) = False) : (term81 m) = False.
Proof. exact (h1). Qed.
Lemma lem149790 (m : nat) (n : nat) : (term83 m n) = (term83 m n).
Proof. exact (eq_refl (term83 m n)). Qed.
Lemma lem149791 (n : nat) (m : nat) (h1 : (term81 m) = True) : (term84 n m) = (term85 m n).
Proof. exact (MK_COMB (@lem149790 m n) (@lem149764 m h1)). Qed.
Lemma lem149792 (m : nat) (n : nat) : (term85 m n) = ((term86 n m) = ((term87 m) = (term65 n))).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem149793 (n : nat) (m : nat) : (term88 n m) = (term88 n m).
Proof. exact (eq_refl (term88 n m)). Qed.
Lemma lem149794 (m : nat) (n : nat) : ((term84 n m) = (term85 m n)) = ((term84 n m) = ((term86 n m) = ((term87 m) = (term65 n)))).
Proof. exact (MK_COMB (@lem149793 n m) (@lem149792 m n)). Qed.
Lemma lem149795 (m : nat) (n : nat) : (term84 n m) = ((term69 n m) = ((term65 m) = (term65 n))).
Proof. exact (eq_refl (term84 n m)). Qed.
Lemma lem149796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149797 (m : nat) (n : nat) : (term88 n m) = (term89 m n).
Proof. exact (MK_COMB (@lem149796) (@lem149795 m n)). Qed.
Lemma lem149798 (m : nat) (n : nat) : ((term86 n m) = ((term87 m) = (term65 n))) = ((term86 n m) = ((term87 m) = (term65 n))).
Proof. exact (eq_refl ((term86 n m) = ((term87 m) = (term65 n)))). Qed.
Lemma lem149799 (m : nat) (n : nat) : ((term84 n m) = ((term86 n m) = ((term87 m) = (term65 n)))) = (((term69 n m) = ((term65 m) = (term65 n))) = ((term86 n m) = ((term87 m) = (term65 n)))).
Proof. exact (MK_COMB (@lem149797 m n) (@lem149798 m n)). Qed.
Lemma lem149800 (m : nat) (n : nat) : ((term84 n m) = (term85 m n)) = (((term69 n m) = ((term65 m) = (term65 n))) = ((term86 n m) = ((term87 m) = (term65 n)))).
Proof. exact (TRANS (@lem149794 m n) (@lem149799 m n)). Qed.
Lemma lem149801 (n : nat) (m : nat) (h1 : (term81 m) = True) : ((term69 n m) = ((term65 m) = (term65 n))) = ((term86 n m) = ((term87 m) = (term65 n))).
Proof. exact (EQ_MP (@lem149800 m n) (@lem149791 n m h1)). Qed.
Lemma lem149802 (n : nat) (m : nat) (h1 : (term81 m) = True) : ((term86 n m) = ((term87 m) = (term65 n))) = ((term69 n m) = ((term65 m) = (term65 n))).
Proof. exact (SYM (@lem149801 n m h1)). Qed.
Lemma lem149803 (m : nat) (n : nat) : (term83 m n) = (term83 m n).
Proof. exact (eq_refl (term83 m n)). Qed.
Lemma lem149804 (n : nat) (m : nat) (h1 : (term81 m) = False) : (term84 n m) = (term90 m n).
Proof. exact (MK_COMB (@lem149803 m n) (@lem149765 m h1)). Qed.
Lemma lem149805 (m : nat) (n : nat) : (term90 m n) = ((term91 n m) = ((term92 m) = (term65 n))).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem149806 (n : nat) (m : nat) : (term88 n m) = (term88 n m).
Proof. exact (eq_refl (term88 n m)). Qed.
Lemma lem149807 (m : nat) (n : nat) : ((term84 n m) = (term90 m n)) = ((term84 n m) = ((term91 n m) = ((term92 m) = (term65 n)))).
Proof. exact (MK_COMB (@lem149806 n m) (@lem149805 m n)). Qed.
Lemma lem149808 (m : nat) (n : nat) : (term84 n m) = ((term69 n m) = ((term65 m) = (term65 n))).
Proof. exact (eq_refl (term84 n m)). Qed.
Lemma lem149809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149810 (m : nat) (n : nat) : (term88 n m) = (term89 m n).
Proof. exact (MK_COMB (@lem149809) (@lem149808 m n)). Qed.
Lemma lem149811 (m : nat) (n : nat) : ((term91 n m) = ((term92 m) = (term65 n))) = ((term91 n m) = ((term92 m) = (term65 n))).
Proof. exact (eq_refl ((term91 n m) = ((term92 m) = (term65 n)))). Qed.
Lemma lem149812 (m : nat) (n : nat) : ((term84 n m) = ((term91 n m) = ((term92 m) = (term65 n)))) = (((term69 n m) = ((term65 m) = (term65 n))) = ((term91 n m) = ((term92 m) = (term65 n)))).
Proof. exact (MK_COMB (@lem149810 m n) (@lem149811 m n)). Qed.
Lemma lem149813 (m : nat) (n : nat) : ((term84 n m) = (term90 m n)) = (((term69 n m) = ((term65 m) = (term65 n))) = ((term91 n m) = ((term92 m) = (term65 n)))).
Proof. exact (TRANS (@lem149807 m n) (@lem149812 m n)). Qed.
Lemma lem149814 (n : nat) (m : nat) (h1 : (term81 m) = False) : ((term69 n m) = ((term65 m) = (term65 n))) = ((term91 n m) = ((term92 m) = (term65 n))).
Proof. exact (EQ_MP (@lem149813 m n) (@lem149804 n m h1)). Qed.
Lemma lem149815 (n : nat) (m : nat) (h1 : (term81 m) = False) : ((term91 n m) = ((term92 m) = (term65 n))) = ((term69 n m) = ((term65 m) = (term65 n))).
Proof. exact (SYM (@lem149814 n m h1)). Qed.
Lemma lem149823 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem149824 (m : nat) : (term87 m) = (term93 m).
Proof. exact (@lem149823 (term93 m)). Qed.
Lemma lem149825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem149826 (m : nat) : (term94 m) = (term95 m).
Proof. exact (MK_COMB (@lem149825) (@lem149824 m)). Qed.
Lemma lem149829 (n : nat) : (term65 n) = (term65 n).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem149830 (m : nat) (n : nat) : (term96 m n) = (term97 m n).
Proof. exact (MK_COMB (@lem149826 m) (@lem149829 n)). Qed.
Lemma lem149833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem149834 (m : nat) (n : nat) : (term98 m n) = (term99 m n).
Proof. exact (MK_COMB (@lem149833) (@lem149830 m n)). Qed.
Lemma lem149840 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem149841 (m : nat) : (term87 m) = (term93 m).
Proof. exact (@lem149840 (term93 m)). Qed.
Lemma lem149842 (n : nat) : (term66 n) = (term66 n).
Proof. exact (eq_refl (term66 n)). Qed.
Lemma lem149843 (n : nat) (m : nat) : (term100 n m) = (term101 n m).
Proof. exact (MK_COMB (@lem149842 n) (@lem149841 m)). Qed.
Lemma lem149846 (n : nat) (m : nat) : (term86 n m) = (term102 n m).
Proof. exact (MK_COMB (@lem149834 m n) (@lem149843 n m)). Qed.
Lemma lem149849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149850 (n : nat) (m : nat) : (term103 n m) = (term104 n m).
Proof. exact (MK_COMB (@lem149849) (@lem149846 n m)). Qed.
Lemma lem149854 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem149855 (m : nat) : (term87 m) = (term93 m).
Proof. exact (@lem149854 (term93 m)). Qed.
Lemma lem149856 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149857 (m : nat) : (term105 m) = (term106 m).
Proof. exact (MK_COMB (@lem149856) (@lem149855 m)). Qed.
Lemma lem149860 (n : nat) : (term65 n) = (term65 n).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem149861 (m : nat) (n : nat) : ((term87 m) = (term65 n)) = ((term93 m) = (term65 n)).
Proof. exact (MK_COMB (@lem149857 m) (@lem149860 n)). Qed.
Lemma lem149864 (m : nat) (n : nat) : ((term86 n m) = ((term87 m) = (term65 n))) = ((term102 n m) = ((term93 m) = (term65 n))).
Proof. exact (MK_COMB (@lem149850 n m) (@lem149861 m n)). Qed.
Lemma lem149867 (m : nat) (n : nat) : ((term102 n m) = ((term93 m) = (term65 n))) = ((term86 n m) = ((term87 m) = (term65 n))).
Proof. exact (SYM (@lem149864 m n)). Qed.
Lemma lem149868 (m : nat) : term107 m.
Proof. exact (@lem9851 (term93 m)). Qed.
Lemma lem149869 (m : nat) : (term107 m) = (term108 m).
Proof. exact (eq_refl (term107 m)). Qed.
Lemma lem149870 (m : nat) : term108 m.
Proof. exact (EQ_MP (@lem149869 m) (@lem149868 m)). Qed.
Lemma lem149871 (m : nat) (h1 : (term93 m) = True) : (term93 m) = True.
Proof. exact (h1). Qed.
Lemma lem149872 (m : nat) (h1 : (term93 m) = False) : (term93 m) = False.
Proof. exact (h1). Qed.
Lemma lem149891 (n : nat) : (term109 n) = (term109 n).
Proof. exact (eq_refl (term109 n)). Qed.
Lemma lem149892 (n : nat) (m : nat) (h1 : (term93 m) = True) : (term110 n m) = (term111 n).
Proof. exact (MK_COMB (@lem149891 n) (@lem149871 m h1)). Qed.
Lemma lem149893 (n : nat) : (term111 n) = ((term112 n) = (True = (term65 n))).
Proof. exact (eq_refl (term111 n)). Qed.
Lemma lem149894 (n : nat) (m : nat) : (term113 n m) = (term113 n m).
Proof. exact (eq_refl (term113 n m)). Qed.
Lemma lem149895 (m : nat) (n : nat) : ((term110 n m) = (term111 n)) = ((term110 n m) = ((term112 n) = (True = (term65 n)))).
Proof. exact (MK_COMB (@lem149894 n m) (@lem149893 n)). Qed.
Lemma lem149896 (m : nat) (n : nat) : (term110 n m) = ((term102 n m) = ((term93 m) = (term65 n))).
Proof. exact (eq_refl (term110 n m)). Qed.
Lemma lem149897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149898 (m : nat) (n : nat) : (term113 n m) = (term114 m n).
Proof. exact (MK_COMB (@lem149897) (@lem149896 m n)). Qed.
Lemma lem149899 (n : nat) : ((term112 n) = (True = (term65 n))) = ((term112 n) = (True = (term65 n))).
Proof. exact (eq_refl ((term112 n) = (True = (term65 n)))). Qed.
Lemma lem149900 (m : nat) (n : nat) : ((term110 n m) = ((term112 n) = (True = (term65 n)))) = (((term102 n m) = ((term93 m) = (term65 n))) = ((term112 n) = (True = (term65 n)))).
Proof. exact (MK_COMB (@lem149898 m n) (@lem149899 n)). Qed.
Lemma lem149901 (m : nat) (n : nat) : ((term110 n m) = (term111 n)) = (((term102 n m) = ((term93 m) = (term65 n))) = ((term112 n) = (True = (term65 n)))).
Proof. exact (TRANS (@lem149895 m n) (@lem149900 m n)). Qed.
Lemma lem149902 (n : nat) (m : nat) (h1 : (term93 m) = True) : ((term102 n m) = ((term93 m) = (term65 n))) = ((term112 n) = (True = (term65 n))).
Proof. exact (EQ_MP (@lem149901 m n) (@lem149892 n m h1)). Qed.
Lemma lem149903 (n : nat) (m : nat) (h1 : (term93 m) = True) : ((term112 n) = (True = (term65 n))) = ((term102 n m) = ((term93 m) = (term65 n))).
Proof. exact (SYM (@lem149902 n m h1)). Qed.
Lemma lem149904 (n : nat) : (term109 n) = (term109 n).
Proof. exact (eq_refl (term109 n)). Qed.
Lemma lem149905 (n : nat) (m : nat) (h1 : (term93 m) = False) : (term110 n m) = (term115 n).
Proof. exact (MK_COMB (@lem149904 n) (@lem149872 m h1)). Qed.
Lemma lem149906 (n : nat) : (term115 n) = ((term116 n) = (False = (term65 n))).
Proof. exact (eq_refl (term115 n)). Qed.
Lemma lem149907 (n : nat) (m : nat) : (term113 n m) = (term113 n m).
Proof. exact (eq_refl (term113 n m)). Qed.
Lemma lem149908 (m : nat) (n : nat) : ((term110 n m) = (term115 n)) = ((term110 n m) = ((term116 n) = (False = (term65 n)))).
Proof. exact (MK_COMB (@lem149907 n m) (@lem149906 n)). Qed.
Lemma lem149909 (m : nat) (n : nat) : (term110 n m) = ((term102 n m) = ((term93 m) = (term65 n))).
Proof. exact (eq_refl (term110 n m)). Qed.
Lemma lem149910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149911 (m : nat) (n : nat) : (term113 n m) = (term114 m n).
Proof. exact (MK_COMB (@lem149910) (@lem149909 m n)). Qed.
Lemma lem149912 (n : nat) : ((term116 n) = (False = (term65 n))) = ((term116 n) = (False = (term65 n))).
Proof. exact (eq_refl ((term116 n) = (False = (term65 n)))). Qed.
Lemma lem149913 (m : nat) (n : nat) : ((term110 n m) = ((term116 n) = (False = (term65 n)))) = (((term102 n m) = ((term93 m) = (term65 n))) = ((term116 n) = (False = (term65 n)))).
Proof. exact (MK_COMB (@lem149911 m n) (@lem149912 n)). Qed.
Lemma lem149914 (m : nat) (n : nat) : ((term110 n m) = (term115 n)) = (((term102 n m) = ((term93 m) = (term65 n))) = ((term116 n) = (False = (term65 n)))).
Proof. exact (TRANS (@lem149908 m n) (@lem149913 m n)). Qed.
Lemma lem149915 (n : nat) (m : nat) (h1 : (term93 m) = False) : ((term102 n m) = ((term93 m) = (term65 n))) = ((term116 n) = (False = (term65 n))).
Proof. exact (EQ_MP (@lem149914 m n) (@lem149905 n m h1)). Qed.
Lemma lem149916 (n : nat) (m : nat) (h1 : (term93 m) = False) : ((term116 n) = (False = (term65 n))) = ((term102 n m) = ((term93 m) = (term65 n))).
Proof. exact (SYM (@lem149915 n m h1)). Qed.
Lemma lem149922 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem149923 (n : nat) : (term117 n) = (term65 n).
Proof. exact (@lem149922 (term65 n)). Qed.
Lemma lem149926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem149927 (n : nat) : (term118 n) = (term119 n).
Proof. exact (MK_COMB (@lem149926) (@lem149923 n)). Qed.
Lemma lem149929 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem149930 (n : nat) : (term120 n) = True.
Proof. exact (@lem149929 (term65 n)). Qed.
Lemma lem149931 (n : nat) : (term112 n) = (term121 n).
Proof. exact (MK_COMB (@lem149927 n) (@lem149930 n)). Qed.
Lemma lem149933 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem149934 (n : nat) : (term121 n) = (term65 n).
Proof. exact (@lem149933 (term65 n)). Qed.
Lemma lem149937 (n : nat) : (term112 n) = (term65 n).
Proof. exact (TRANS (@lem149931 n) (@lem149934 n)). Qed.
Lemma lem149938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149939 (n : nat) : (term122 n) = (term72 n).
Proof. exact (MK_COMB (@lem149938) (@lem149937 n)). Qed.
Lemma lem149941 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem149942 (n : nat) : (True = (term65 n)) = (term65 n).
Proof. exact (@lem149941 (term65 n)). Qed.
Lemma lem149945 (n : nat) : ((term112 n) = (True = (term65 n))) = ((term65 n) = (term65 n)).
Proof. exact (MK_COMB (@lem149939 n) (@lem149942 n)). Qed.
Lemma lem149947 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem149948 (x : Prop) : (x = x) = True.
Proof. exact (@lem149947 Prop x). Qed.
Lemma lem149949 (n : nat) : ((term65 n) = (term65 n)) = True.
Proof. exact (@lem149948 (term65 n)). Qed.
Lemma lem149950 (n : nat) : ((term112 n) = (True = (term65 n))) = True.
Proof. exact (TRANS (@lem149945 n) (@lem149949 n)). Qed.
Lemma lem149951 (n : nat) : True = ((term112 n) = (True = (term65 n))).
Proof. exact (SYM (@lem149950 n)). Qed.
Lemma lem149952 (n : nat) : (term112 n) = (True = (term65 n)).
Proof. exact (EQ_MP (@lem149951 n) (@lem0)). Qed.
Lemma lem149958 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem149959 (n : nat) : (term123 n) = True.
Proof. exact (@lem149958 (term65 n)). Qed.
Lemma lem149960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem149961 (n : nat) : (term124 n) = (and True).
Proof. exact (MK_COMB (@lem149960) (@lem149959 n)). Qed.
Lemma lem149963 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem149964 (n : nat) : (term125 n) = (term126 n).
Proof. exact (@lem149963 (term65 n)). Qed.
Lemma lem149967 (n : nat) : (term116 n) = (term127 n).
Proof. exact (MK_COMB (@lem149961 n) (@lem149964 n)). Qed.
Lemma lem149969 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem149970 (n : nat) : (term127 n) = (term126 n).
Proof. exact (@lem149969 (term126 n)). Qed.
Lemma lem149973 (n : nat) : (term116 n) = (term126 n).
Proof. exact (TRANS (@lem149967 n) (@lem149970 n)). Qed.
Lemma lem149974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149975 (n : nat) : (term128 n) = (term129 n).
Proof. exact (MK_COMB (@lem149974) (@lem149973 n)). Qed.
Lemma lem149977 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem149978 (n : nat) : (False = (term65 n)) = (term126 n).
Proof. exact (@lem149977 (term65 n)). Qed.
Lemma lem149981 (n : nat) : ((term116 n) = (False = (term65 n))) = ((term126 n) = (term126 n)).
Proof. exact (MK_COMB (@lem149975 n) (@lem149978 n)). Qed.
Lemma lem149983 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem149984 (x : Prop) : (x = x) = True.
Proof. exact (@lem149983 Prop x). Qed.
Lemma lem149985 (n : nat) : ((term126 n) = (term126 n)) = True.
Proof. exact (@lem149984 (term126 n)). Qed.
Lemma lem149986 (n : nat) : ((term116 n) = (False = (term65 n))) = True.
Proof. exact (TRANS (@lem149981 n) (@lem149985 n)). Qed.
Lemma lem149987 (n : nat) : True = ((term116 n) = (False = (term65 n))).
Proof. exact (SYM (@lem149986 n)). Qed.
Lemma lem149988 (n : nat) : (term116 n) = (False = (term65 n)).
Proof. exact (EQ_MP (@lem149987 n) (@lem0)). Qed.
Lemma lem149989 (n : nat) (m : nat) (h1 : (term93 m) = False) : (term102 n m) = ((term93 m) = (term65 n)).
Proof. exact (EQ_MP (@lem149916 n m h1) (@lem149988 n)). Qed.
Lemma lem149990 (n : nat) (m : nat) (h1 : (term93 m) = True) : (term102 n m) = ((term93 m) = (term65 n)).
Proof. exact (EQ_MP (@lem149903 n m h1) (@lem149952 n)). Qed.
Lemma lem149992 (m : nat) (n : nat) : (term102 n m) = ((term93 m) = (term65 n)).
Proof. exact (or_elim (@lem149870 m) (fun h0 : (term93 m) = True => @lem149990 n m h0) (fun h0 : (term93 m) = False => @lem149989 n m h0)). Qed.
Lemma lem149993 (m : nat) (n : nat) : (term86 n m) = ((term87 m) = (term65 n)).
Proof. exact (EQ_MP (@lem149867 m n) (@lem149992 m n)). Qed.
Lemma lem150001 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem150002 (m : nat) : (term92 m) = False.
Proof. exact (@lem150001 (term93 m)). Qed.
Lemma lem150003 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem150004 (m : nat) : (term130 m) = (imp False).
Proof. exact (MK_COMB (@lem150003) (@lem150002 m)). Qed.
Lemma lem150007 (n : nat) : (term65 n) = (term65 n).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem150008 (m : nat) (n : nat) : (term131 m n) = (term123 n).
Proof. exact (MK_COMB (@lem150004 m) (@lem150007 n)). Qed.
Lemma lem150010 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem150011 (n : nat) : (term123 n) = True.
Proof. exact (@lem150010 (term65 n)). Qed.
Lemma lem150012 (m : nat) (n : nat) : (term131 m n) = True.
Proof. exact (TRANS (@lem150008 m n) (@lem150011 n)). Qed.
Lemma lem150013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem150014 (m : nat) (n : nat) : (term132 m n) = (and True).
Proof. exact (MK_COMB (@lem150013) (@lem150012 m n)). Qed.
Lemma lem150020 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem150021 (m : nat) : (term92 m) = False.
Proof. exact (@lem150020 (term93 m)). Qed.
Lemma lem150022 (n : nat) : (term66 n) = (term66 n).
Proof. exact (eq_refl (term66 n)). Qed.
Lemma lem150023 (m : nat) (n : nat) : (term133 n m) = (term125 n).
Proof. exact (MK_COMB (@lem150022 n) (@lem150021 m)). Qed.
Lemma lem150025 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem150026 (n : nat) : (term125 n) = (term126 n).
Proof. exact (@lem150025 (term65 n)). Qed.
Lemma lem150029 (m : nat) (n : nat) : (term133 n m) = (term126 n).
Proof. exact (TRANS (@lem150023 m n) (@lem150026 n)). Qed.
Lemma lem150030 (m : nat) (n : nat) : (term91 n m) = (term127 n).
Proof. exact (MK_COMB (@lem150014 m n) (@lem150029 m n)). Qed.
Lemma lem150032 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem150033 (n : nat) : (term127 n) = (term126 n).
Proof. exact (@lem150032 (term126 n)). Qed.
Lemma lem150036 (m : nat) (n : nat) : (term91 n m) = (term126 n).
Proof. exact (TRANS (@lem150030 m n) (@lem150033 n)). Qed.
Lemma lem150037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150038 (m : nat) (n : nat) : (term134 n m) = (term129 n).
Proof. exact (MK_COMB (@lem150037) (@lem150036 m n)). Qed.
Lemma lem150042 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem150043 (m : nat) : (term92 m) = False.
Proof. exact (@lem150042 (term93 m)). Qed.
Lemma lem150044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150045 (m : nat) : (term135 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem150044) (@lem150043 m)). Qed.
Lemma lem150048 (n : nat) : (term65 n) = (term65 n).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem150049 (m : nat) (n : nat) : ((term92 m) = (term65 n)) = (False = (term65 n)).
Proof. exact (MK_COMB (@lem150045 m) (@lem150048 n)). Qed.
Lemma lem150051 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem150052 (n : nat) : (False = (term65 n)) = (term126 n).
Proof. exact (@lem150051 (term65 n)). Qed.
Lemma lem150055 (m : nat) (n : nat) : ((term92 m) = (term65 n)) = (term126 n).
Proof. exact (TRANS (@lem150049 m n) (@lem150052 n)). Qed.
Lemma lem150056 (m : nat) (n : nat) : ((term91 n m) = ((term92 m) = (term65 n))) = ((term126 n) = (term126 n)).
Proof. exact (MK_COMB (@lem150038 m n) (@lem150055 m n)). Qed.
Lemma lem150058 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem150059 (x : Prop) : (x = x) = True.
Proof. exact (@lem150058 Prop x). Qed.
Lemma lem150060 (n : nat) : ((term126 n) = (term126 n)) = True.
Proof. exact (@lem150059 (term126 n)). Qed.
Lemma lem150061 (m : nat) (n : nat) : ((term91 n m) = ((term92 m) = (term65 n))) = True.
Proof. exact (TRANS (@lem150056 m n) (@lem150060 n)). Qed.
Lemma lem150062 (m : nat) (n : nat) : True = ((term91 n m) = ((term92 m) = (term65 n))).
Proof. exact (SYM (@lem150061 m n)). Qed.
Lemma lem150063 (m : nat) (n : nat) : (term91 n m) = ((term92 m) = (term65 n)).
Proof. exact (EQ_MP (@lem150062 m n) (@lem0)). Qed.
Lemma lem150064 (n : nat) (m : nat) (h1 : (term81 m) = False) : (term69 n m) = ((term65 m) = (term65 n)).
Proof. exact (EQ_MP (@lem149815 n m h1) (@lem150063 m n)). Qed.
Lemma lem150065 (n : nat) (m : nat) (h1 : (term81 m) = True) : (term69 n m) = ((term65 m) = (term65 n)).
Proof. exact (EQ_MP (@lem149802 n m h1) (@lem149993 m n)). Qed.
Lemma lem150068 (m : nat) (n : nat) : (term69 n m) = ((term65 m) = (term65 n)).
Proof. exact (or_elim (@lem149763 m) (fun h0 : (term81 m) = True => @lem150065 n m h0) (fun h0 : (term81 m) = False => @lem150064 n m h0)). Qed.
Lemma lem150089 (x : nat) : term136 x.
Proof. exact (@lem9851 (term137 x)). Qed.
Lemma lem150090 (x : nat) : (term136 x) = (term138 x).
Proof. exact (eq_refl (term136 x)). Qed.
Lemma lem150091 (x : nat) : term138 x.
Proof. exact (EQ_MP (@lem150090 x) (@lem150089 x)). Qed.
Lemma lem150092 (x : nat) (h1 : (term137 x) = True) : (term137 x) = True.
Proof. exact (h1). Qed.
Lemma lem150093 (x : nat) (h1 : (term137 x) = False) : (term137 x) = False.
Proof. exact (h1). Qed.
Lemma lem150114 (x : nat) (n : nat) (m : nat) : (term139 x n m) = (term139 x n m).
Proof. exact (eq_refl (term139 x n m)). Qed.
Lemma lem150115 (n : nat) (m : nat) (x : nat) (h1 : (term137 x) = True) : (term140 n m x) = (term141 x n m).
Proof. exact (MK_COMB (@lem150114 x n m) (@lem150092 x h1)). Qed.
Lemma lem150116 (x : nat) (n : nat) (m : nat) : (term141 x n m) = ((term142 x n m) = (term143 x n m)).
Proof. exact (eq_refl (term141 x n m)). Qed.
Lemma lem150117 (n : nat) (m : nat) (x : nat) : (term144 n m x) = (term144 n m x).
Proof. exact (eq_refl (term144 n m x)). Qed.
Lemma lem150118 (x : nat) (n : nat) (m : nat) : ((term140 n m x) = (term141 x n m)) = ((term140 n m x) = ((term142 x n m) = (term143 x n m))).
Proof. exact (MK_COMB (@lem150117 n m x) (@lem150116 x n m)). Qed.
Lemma lem150119 (x : nat) (n : nat) (m : nat) : (term140 n m x) = ((term77 x n m) = (term79 x n m)).
Proof. exact (eq_refl (term140 n m x)). Qed.
Lemma lem150120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150121 (x : nat) (n : nat) (m : nat) : (term144 n m x) = (term145 x n m).
Proof. exact (MK_COMB (@lem150120) (@lem150119 x n m)). Qed.
Lemma lem150122 (x : nat) (n : nat) (m : nat) : ((term142 x n m) = (term143 x n m)) = ((term142 x n m) = (term143 x n m)).
Proof. exact (eq_refl ((term142 x n m) = (term143 x n m))). Qed.
Lemma lem150123 (x : nat) (n : nat) (m : nat) : ((term140 n m x) = ((term142 x n m) = (term143 x n m))) = (((term77 x n m) = (term79 x n m)) = ((term142 x n m) = (term143 x n m))).
Proof. exact (MK_COMB (@lem150121 x n m) (@lem150122 x n m)). Qed.
Lemma lem150124 (x : nat) (n : nat) (m : nat) : ((term140 n m x) = (term141 x n m)) = (((term77 x n m) = (term79 x n m)) = ((term142 x n m) = (term143 x n m))).
Proof. exact (TRANS (@lem150118 x n m) (@lem150123 x n m)). Qed.
Lemma lem150125 (n : nat) (m : nat) (x : nat) (h1 : (term137 x) = True) : ((term77 x n m) = (term79 x n m)) = ((term142 x n m) = (term143 x n m)).
Proof. exact (EQ_MP (@lem150124 x n m) (@lem150115 n m x h1)). Qed.
Lemma lem150126 (n : nat) (m : nat) (x : nat) (h1 : (term137 x) = True) : ((term142 x n m) = (term143 x n m)) = ((term77 x n m) = (term79 x n m)).
Proof. exact (SYM (@lem150125 n m x h1)). Qed.
Lemma lem150127 (x : nat) (n : nat) (m : nat) : (term139 x n m) = (term139 x n m).
Proof. exact (eq_refl (term139 x n m)). Qed.
Lemma lem150128 (n : nat) (m : nat) (x : nat) (h1 : (term137 x) = False) : (term140 n m x) = (term146 x n m).
Proof. exact (MK_COMB (@lem150127 x n m) (@lem150093 x h1)). Qed.
Lemma lem150129 (x : nat) (n : nat) (m : nat) : (term146 x n m) = ((term147 x n m) = (term148 x n m)).
Proof. exact (eq_refl (term146 x n m)). Qed.
Lemma lem150130 (n : nat) (m : nat) (x : nat) : (term144 n m x) = (term144 n m x).
Proof. exact (eq_refl (term144 n m x)). Qed.
Lemma lem150131 (x : nat) (n : nat) (m : nat) : ((term140 n m x) = (term146 x n m)) = ((term140 n m x) = ((term147 x n m) = (term148 x n m))).
Proof. exact (MK_COMB (@lem150130 n m x) (@lem150129 x n m)). Qed.
Lemma lem150132 (x : nat) (n : nat) (m : nat) : (term140 n m x) = ((term77 x n m) = (term79 x n m)).
Proof. exact (eq_refl (term140 n m x)). Qed.
Lemma lem150133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150134 (x : nat) (n : nat) (m : nat) : (term144 n m x) = (term145 x n m).
Proof. exact (MK_COMB (@lem150133) (@lem150132 x n m)). Qed.
Lemma lem150135 (x : nat) (n : nat) (m : nat) : ((term147 x n m) = (term148 x n m)) = ((term147 x n m) = (term148 x n m)).
Proof. exact (eq_refl ((term147 x n m) = (term148 x n m))). Qed.
Lemma lem150136 (x : nat) (n : nat) (m : nat) : ((term140 n m x) = ((term147 x n m) = (term148 x n m))) = (((term77 x n m) = (term79 x n m)) = ((term147 x n m) = (term148 x n m))).
Proof. exact (MK_COMB (@lem150134 x n m) (@lem150135 x n m)). Qed.
Lemma lem150137 (x : nat) (n : nat) (m : nat) : ((term140 n m x) = (term146 x n m)) = (((term77 x n m) = (term79 x n m)) = ((term147 x n m) = (term148 x n m))).
Proof. exact (TRANS (@lem150131 x n m) (@lem150136 x n m)). Qed.
Lemma lem150138 (n : nat) (m : nat) (x : nat) (h1 : (term137 x) = False) : ((term77 x n m) = (term79 x n m)) = ((term147 x n m) = (term148 x n m)).
Proof. exact (EQ_MP (@lem150137 x n m) (@lem150128 n m x h1)). Qed.
Lemma lem150139 (n : nat) (m : nat) (x : nat) (h1 : (term137 x) = False) : ((term147 x n m) = (term148 x n m)) = ((term77 x n m) = (term79 x n m)).
Proof. exact (SYM (@lem150138 n m x h1)). Qed.
Lemma lem150147 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem150148 (x : nat) : (term149 x) = (term150 x).
Proof. exact (@lem150147 (term150 x)). Qed.
Lemma lem150149 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem150150 (x : nat) : (term151 x) = (term152 x).
Proof. exact (MK_COMB (@lem150149) (@lem150148 x)). Qed.
Lemma lem150151 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem150152 (x : nat) (m : nat) (n : nat) : (term153 x m n) = (term154 x m n).
Proof. exact (MK_COMB (@lem150150 x) (@lem150151 m n)). Qed.
Lemma lem150155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem150156 (x : nat) (m : nat) (n : nat) : (term155 x m n) = (term156 x m n).
Proof. exact (MK_COMB (@lem150155) (@lem150152 x m n)). Qed.
Lemma lem150160 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem150161 (x : nat) : (term149 x) = (term150 x).
Proof. exact (@lem150160 (term150 x)). Qed.
Lemma lem150162 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem150163 (x : nat) : (term151 x) = (term152 x).
Proof. exact (MK_COMB (@lem150162) (@lem150161 x)). Qed.
Lemma lem150164 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem150165 (x : nat) (n : nat) (m : nat) : (term153 x n m) = (term154 x n m).
Proof. exact (MK_COMB (@lem150163 x) (@lem150164 n m)). Qed.
Lemma lem150168 (x : nat) (n : nat) (m : nat) : (term142 x n m) = (term157 x n m).
Proof. exact (MK_COMB (@lem150156 x m n) (@lem150165 x n m)). Qed.
Lemma lem150171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150172 (x : nat) (n : nat) (m : nat) : (term158 x n m) = (term159 x n m).
Proof. exact (MK_COMB (@lem150171) (@lem150168 x n m)). Qed.
Lemma lem150176 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem150177 (x : nat) : (term149 x) = (term150 x).
Proof. exact (@lem150176 (term150 x)). Qed.
Lemma lem150178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem150179 (x : nat) : (term151 x) = (term152 x).
Proof. exact (MK_COMB (@lem150178) (@lem150177 x)). Qed.
Lemma lem150182 (n : nat) (m : nat) : (term0 n m) = (term0 n m).
Proof. exact (eq_refl (term0 n m)). Qed.
Lemma lem150183 (x : nat) (n : nat) (m : nat) : (term143 x n m) = (term160 x n m).
Proof. exact (MK_COMB (@lem150179 x) (@lem150182 n m)). Qed.
Lemma lem150186 (x : nat) (n : nat) (m : nat) : ((term142 x n m) = (term143 x n m)) = ((term157 x n m) = (term160 x n m)).
Proof. exact (MK_COMB (@lem150172 x n m) (@lem150183 x n m)). Qed.
Lemma lem150189 (x : nat) (n : nat) (m : nat) : ((term157 x n m) = (term160 x n m)) = ((term142 x n m) = (term143 x n m)).
Proof. exact (SYM (@lem150186 x n m)). Qed.
Lemma lem150190 (x : nat) : term161 x.
Proof. exact (@lem9851 (term150 x)). Qed.
Lemma lem150191 (x : nat) : (term161 x) = (term162 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem150192 (x : nat) : term162 x.
Proof. exact (EQ_MP (@lem150191 x) (@lem150190 x)). Qed.
Lemma lem150193 (x : nat) (h1 : (term150 x) = True) : (term150 x) = True.
Proof. exact (h1). Qed.
Lemma lem150194 (x : nat) (h1 : (term150 x) = False) : (term150 x) = False.
Proof. exact (h1). Qed.
Lemma lem150209 (n : nat) (m : nat) : (term163 n m) = (term163 n m).
Proof. exact (eq_refl (term163 n m)). Qed.
Lemma lem150210 (n : nat) (m : nat) (x : nat) (h1 : (term150 x) = True) : (term164 n m x) = (term165 n m).
Proof. exact (MK_COMB (@lem150209 n m) (@lem150193 x h1)). Qed.
Lemma lem150211 (n : nat) (m : nat) : (term165 n m) = ((term166 n m) = (term167 n m)).
Proof. exact (eq_refl (term165 n m)). Qed.
Lemma lem150212 (n : nat) (m : nat) (x : nat) : (term168 n m x) = (term168 n m x).
Proof. exact (eq_refl (term168 n m x)). Qed.
Lemma lem150213 (x : nat) (n : nat) (m : nat) : ((term164 n m x) = (term165 n m)) = ((term164 n m x) = ((term166 n m) = (term167 n m))).
Proof. exact (MK_COMB (@lem150212 n m x) (@lem150211 n m)). Qed.
Lemma lem150214 (x : nat) (n : nat) (m : nat) : (term164 n m x) = ((term157 x n m) = (term160 x n m)).
Proof. exact (eq_refl (term164 n m x)). Qed.
Lemma lem150215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150216 (x : nat) (n : nat) (m : nat) : (term168 n m x) = (term169 x n m).
Proof. exact (MK_COMB (@lem150215) (@lem150214 x n m)). Qed.
Lemma lem150217 (n : nat) (m : nat) : ((term166 n m) = (term167 n m)) = ((term166 n m) = (term167 n m)).
Proof. exact (eq_refl ((term166 n m) = (term167 n m))). Qed.
Lemma lem150218 (x : nat) (n : nat) (m : nat) : ((term164 n m x) = ((term166 n m) = (term167 n m))) = (((term157 x n m) = (term160 x n m)) = ((term166 n m) = (term167 n m))).
Proof. exact (MK_COMB (@lem150216 x n m) (@lem150217 n m)). Qed.
Lemma lem150219 (x : nat) (n : nat) (m : nat) : ((term164 n m x) = (term165 n m)) = (((term157 x n m) = (term160 x n m)) = ((term166 n m) = (term167 n m))).
Proof. exact (TRANS (@lem150213 x n m) (@lem150218 x n m)). Qed.
Lemma lem150220 (n : nat) (m : nat) (x : nat) (h1 : (term150 x) = True) : ((term157 x n m) = (term160 x n m)) = ((term166 n m) = (term167 n m)).
Proof. exact (EQ_MP (@lem150219 x n m) (@lem150210 n m x h1)). Qed.
Lemma lem150221 (n : nat) (m : nat) (x : nat) (h1 : (term150 x) = True) : ((term166 n m) = (term167 n m)) = ((term157 x n m) = (term160 x n m)).
Proof. exact (SYM (@lem150220 n m x h1)). Qed.
Lemma lem150222 (n : nat) (m : nat) : (term163 n m) = (term163 n m).
Proof. exact (eq_refl (term163 n m)). Qed.
Lemma lem150223 (n : nat) (m : nat) (x : nat) (h1 : (term150 x) = False) : (term164 n m x) = (term170 n m).
Proof. exact (MK_COMB (@lem150222 n m) (@lem150194 x h1)). Qed.
Lemma lem150224 (n : nat) (m : nat) : (term170 n m) = ((term171 n m) = (term172 n m)).
Proof. exact (eq_refl (term170 n m)). Qed.
Lemma lem150225 (n : nat) (m : nat) (x : nat) : (term168 n m x) = (term168 n m x).
Proof. exact (eq_refl (term168 n m x)). Qed.
Lemma lem150226 (x : nat) (n : nat) (m : nat) : ((term164 n m x) = (term170 n m)) = ((term164 n m x) = ((term171 n m) = (term172 n m))).
Proof. exact (MK_COMB (@lem150225 n m x) (@lem150224 n m)). Qed.
Lemma lem150227 (x : nat) (n : nat) (m : nat) : (term164 n m x) = ((term157 x n m) = (term160 x n m)).
Proof. exact (eq_refl (term164 n m x)). Qed.
Lemma lem150228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150229 (x : nat) (n : nat) (m : nat) : (term168 n m x) = (term169 x n m).
Proof. exact (MK_COMB (@lem150228) (@lem150227 x n m)). Qed.
Lemma lem150230 (n : nat) (m : nat) : ((term171 n m) = (term172 n m)) = ((term171 n m) = (term172 n m)).
Proof. exact (eq_refl ((term171 n m) = (term172 n m))). Qed.
Lemma lem150231 (x : nat) (n : nat) (m : nat) : ((term164 n m x) = ((term171 n m) = (term172 n m))) = (((term157 x n m) = (term160 x n m)) = ((term171 n m) = (term172 n m))).
Proof. exact (MK_COMB (@lem150229 x n m) (@lem150230 n m)). Qed.
Lemma lem150232 (x : nat) (n : nat) (m : nat) : ((term164 n m x) = (term170 n m)) = (((term157 x n m) = (term160 x n m)) = ((term171 n m) = (term172 n m))).
Proof. exact (TRANS (@lem150226 x n m) (@lem150231 x n m)). Qed.
Lemma lem150233 (n : nat) (m : nat) (x : nat) (h1 : (term150 x) = False) : ((term157 x n m) = (term160 x n m)) = ((term171 n m) = (term172 n m)).
Proof. exact (EQ_MP (@lem150232 x n m) (@lem150223 n m x h1)). Qed.
Lemma lem150234 (n : nat) (m : nat) (x : nat) (h1 : (term150 x) = False) : ((term171 n m) = (term172 n m)) = ((term157 x n m) = (term160 x n m)).
Proof. exact (SYM (@lem150233 n m x h1)). Qed.
Lemma lem150240 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem150241 (m : nat) (n : nat) : (term173 m n) = True.
Proof. exact (@lem150240 (Peano.le m n)). Qed.
Lemma lem150242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem150243 (m : nat) (n : nat) : (term174 m n) = (and True).
Proof. exact (MK_COMB (@lem150242) (@lem150241 m n)). Qed.
Lemma lem150245 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem150246 (n : nat) (m : nat) : (term173 n m) = True.
Proof. exact (@lem150245 (Peano.le n m)). Qed.
Lemma lem150247 (n : nat) (m : nat) : (term166 n m) = (True /\ True).
Proof. exact (MK_COMB (@lem150243 m n) (@lem150246 n m)). Qed.
Lemma lem150249 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem150250 : (True /\ True) = True.
Proof. exact (@lem150249 True). Qed.
Lemma lem150251 (n : nat) (m : nat) : (term166 n m) = True.
Proof. exact (TRANS (@lem150247 n m) (@lem150250)). Qed.
Lemma lem150252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150253 (n : nat) (m : nat) : (term175 n m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem150252) (@lem150251 n m)). Qed.
Lemma lem150255 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem150256 (n : nat) (m : nat) : (term167 n m) = True.
Proof. exact (@lem150255 (term0 n m)). Qed.
Lemma lem150257 (n : nat) (m : nat) : ((term166 n m) = (term167 n m)) = (True = True).
Proof. exact (MK_COMB (@lem150253 n m) (@lem150256 n m)). Qed.
Lemma lem150259 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem150260 : (True = True) = True.
Proof. exact (@lem150259 True). Qed.
Lemma lem150261 (n : nat) (m : nat) : ((term166 n m) = (term167 n m)) = True.
Proof. exact (TRANS (@lem150257 n m) (@lem150260)). Qed.
Lemma lem150262 (n : nat) (m : nat) : True = ((term166 n m) = (term167 n m)).
Proof. exact (SYM (@lem150261 n m)). Qed.
Lemma lem150263 (n : nat) (m : nat) : (term166 n m) = (term167 n m).
Proof. exact (EQ_MP (@lem150262 n m) (@lem0)). Qed.
Lemma lem150269 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem150270 (m : nat) (n : nat) : (term176 m n) = (Peano.le m n).
Proof. exact (@lem150269 (Peano.le m n)). Qed.
Lemma lem150271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem150272 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (MK_COMB (@lem150271) (@lem150270 m n)). Qed.
Lemma lem150274 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem150275 (n : nat) (m : nat) : (term176 n m) = (Peano.le n m).
Proof. exact (@lem150274 (Peano.le n m)). Qed.
Lemma lem150276 (n : nat) (m : nat) : (term171 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem150272 m n) (@lem150275 n m)). Qed.
Lemma lem150279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150280 (n : nat) (m : nat) : (term179 n m) = (term180 n m).
Proof. exact (MK_COMB (@lem150279) (@lem150276 n m)). Qed.
Lemma lem150282 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem150283 (n : nat) (m : nat) : (term172 n m) = (term0 n m).
Proof. exact (@lem150282 (term0 n m)). Qed.
Lemma lem150286 (n : nat) (m : nat) : ((term171 n m) = (term172 n m)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem150280 n m) (@lem150283 n m)). Qed.
Lemma lem150288 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem150289 (x : Prop) : (x = x) = True.
Proof. exact (@lem150288 Prop x). Qed.
Lemma lem150290 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem150289 (term0 n m)). Qed.
Lemma lem150291 (n : nat) (m : nat) : ((term171 n m) = (term172 n m)) = True.
Proof. exact (TRANS (@lem150286 n m) (@lem150290 n m)). Qed.
Lemma lem150292 (n : nat) (m : nat) : True = ((term171 n m) = (term172 n m)).
Proof. exact (SYM (@lem150291 n m)). Qed.
Lemma lem150293 (n : nat) (m : nat) : (term171 n m) = (term172 n m).
Proof. exact (EQ_MP (@lem150292 n m) (@lem0)). Qed.
Lemma lem150294 (n : nat) (m : nat) (x : nat) (h1 : (term150 x) = False) : (term157 x n m) = (term160 x n m).
Proof. exact (EQ_MP (@lem150234 n m x h1) (@lem150293 n m)). Qed.
Lemma lem150295 (n : nat) (m : nat) (x : nat) (h1 : (term150 x) = True) : (term157 x n m) = (term160 x n m).
Proof. exact (EQ_MP (@lem150221 n m x h1) (@lem150263 n m)). Qed.
Lemma lem150297 (x : nat) (n : nat) (m : nat) : (term157 x n m) = (term160 x n m).
Proof. exact (or_elim (@lem150192 x) (fun h0 : (term150 x) = True => @lem150295 n m x h0) (fun h0 : (term150 x) = False => @lem150294 n m x h0)). Qed.
Lemma lem150298 (x : nat) (n : nat) (m : nat) : (term142 x n m) = (term143 x n m).
Proof. exact (EQ_MP (@lem150189 x n m) (@lem150297 x n m)). Qed.
Lemma lem150306 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem150307 (x : nat) : (term181 x) = False.
Proof. exact (@lem150306 (term150 x)). Qed.
Lemma lem150308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem150309 (x : nat) : (term182 x) = (or False).
Proof. exact (MK_COMB (@lem150308) (@lem150307 x)). Qed.
Lemma lem150310 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem150311 (x : nat) (m : nat) (n : nat) : (term183 x m n) = (term176 m n).
Proof. exact (MK_COMB (@lem150309 x) (@lem150310 m n)). Qed.
Lemma lem150313 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem150314 (m : nat) (n : nat) : (term176 m n) = (Peano.le m n).
Proof. exact (@lem150313 (Peano.le m n)). Qed.
Lemma lem150315 (x : nat) (m : nat) (n : nat) : (term183 x m n) = (Peano.le m n).
Proof. exact (TRANS (@lem150311 x m n) (@lem150314 m n)). Qed.
Lemma lem150316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem150317 (x : nat) (m : nat) (n : nat) : (term184 x m n) = (term178 m n).
Proof. exact (MK_COMB (@lem150316) (@lem150315 x m n)). Qed.
Lemma lem150321 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem150322 (x : nat) : (term181 x) = False.
Proof. exact (@lem150321 (term150 x)). Qed.
Lemma lem150323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem150324 (x : nat) : (term182 x) = (or False).
Proof. exact (MK_COMB (@lem150323) (@lem150322 x)). Qed.
Lemma lem150325 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem150326 (x : nat) (n : nat) (m : nat) : (term183 x n m) = (term176 n m).
Proof. exact (MK_COMB (@lem150324 x) (@lem150325 n m)). Qed.
Lemma lem150328 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem150329 (n : nat) (m : nat) : (term176 n m) = (Peano.le n m).
Proof. exact (@lem150328 (Peano.le n m)). Qed.
Lemma lem150330 (x : nat) (n : nat) (m : nat) : (term183 x n m) = (Peano.le n m).
Proof. exact (TRANS (@lem150326 x n m) (@lem150329 n m)). Qed.
Lemma lem150331 (x : nat) (n : nat) (m : nat) : (term147 x n m) = (term0 n m).
Proof. exact (MK_COMB (@lem150317 x m n) (@lem150330 x n m)). Qed.
Lemma lem150334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150335 (x : nat) (n : nat) (m : nat) : (term185 x n m) = (term180 n m).
Proof. exact (MK_COMB (@lem150334) (@lem150331 x n m)). Qed.
Lemma lem150339 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem150340 (x : nat) : (term181 x) = False.
Proof. exact (@lem150339 (term150 x)). Qed.
Lemma lem150341 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem150342 (x : nat) : (term182 x) = (or False).
Proof. exact (MK_COMB (@lem150341) (@lem150340 x)). Qed.
Lemma lem150345 (n : nat) (m : nat) : (term0 n m) = (term0 n m).
Proof. exact (eq_refl (term0 n m)). Qed.
Lemma lem150346 (x : nat) (n : nat) (m : nat) : (term148 x n m) = (term172 n m).
Proof. exact (MK_COMB (@lem150342 x) (@lem150345 n m)). Qed.
Lemma lem150348 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem150349 (n : nat) (m : nat) : (term172 n m) = (term0 n m).
Proof. exact (@lem150348 (term0 n m)). Qed.
Lemma lem150352 (x : nat) (n : nat) (m : nat) : (term148 x n m) = (term0 n m).
Proof. exact (TRANS (@lem150346 x n m) (@lem150349 n m)). Qed.
Lemma lem150353 (x : nat) (n : nat) (m : nat) : ((term147 x n m) = (term148 x n m)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem150335 x n m) (@lem150352 x n m)). Qed.
Lemma lem150355 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem150356 (x : Prop) : (x = x) = True.
Proof. exact (@lem150355 Prop x). Qed.
Lemma lem150357 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem150356 (term0 n m)). Qed.
Lemma lem150358 (x : nat) (n : nat) (m : nat) : ((term147 x n m) = (term148 x n m)) = True.
Proof. exact (TRANS (@lem150353 x n m) (@lem150357 n m)). Qed.
Lemma lem150359 (x : nat) (n : nat) (m : nat) : True = ((term147 x n m) = (term148 x n m)).
Proof. exact (SYM (@lem150358 x n m)). Qed.
Lemma lem150360 (x : nat) (n : nat) (m : nat) : (term147 x n m) = (term148 x n m).
Proof. exact (EQ_MP (@lem150359 x n m) (@lem0)). Qed.
Lemma lem150361 (n : nat) (m : nat) (x : nat) (h1 : (term137 x) = False) : (term77 x n m) = (term79 x n m).
Proof. exact (EQ_MP (@lem150139 n m x h1) (@lem150360 x n m)). Qed.
Lemma lem150362 (n : nat) (m : nat) (x : nat) (h1 : (term137 x) = True) : (term77 x n m) = (term79 x n m).
Proof. exact (EQ_MP (@lem150126 n m x h1) (@lem150298 x n m)). Qed.
Lemma lem150365 (x : nat) (n : nat) (m : nat) : (term77 x n m) = (term79 x n m).
Proof. exact (or_elim (@lem150091 x) (fun h0 : (term137 x) = True => @lem150362 n m x h0) (fun h0 : (term137 x) = False => @lem150361 n m x h0)). Qed.
Lemma lem150366 (x : nat) (m : nat) (n : nat) : (term63 x n m) = (term22 x m n).
Proof. exact (EQ_MP (@lem149736 x m n) (@lem150365 x n m)). Qed.
Lemma lem150367 (m : nat) (n : nat) : (term57 n m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0))).
Proof. exact (EQ_MP (@lem149667 m n) (@lem150068 m n)). Qed.
Lemma lem150370 (m : nat) (n : nat) (x : nat) (h1 : term36 x) : (term11 n x m) = (term22 x m n).
Proof. exact (EQ_MP (@lem149577 m n x h1) (@lem150366 x m n)). Qed.
Lemma lem150371 (m : nat) (n : nat) (x : nat) (h1 : term36 x) : (term36 x) = ((term11 n x m) = (term22 x m n)).
Proof. exact (prop_ext (fun h2 : term36 x => @lem150370 m n x h1) (fun h2 : (term11 n x m) = (term22 x m n) => @lem149292 x h1)). Qed.
Lemma lem150372 (m : nat) (n : nat) (x : nat) (h1 : term36 x) : (term11 n x m) = (term22 x m n).
Proof. exact (EQ_MP (@lem150371 m n x h1) (@lem149292 x h1)). Qed.
Lemma lem150373 (x : nat) (m : nat) (n : nat) : term26 x m n.
Proof. exact (fun h0 : term36 x => @lem150372 m n x h0). Qed.
Lemma lem150374 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term11 n x m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0))).
Proof. exact (EQ_MP (@lem149464 m n x h1) (@lem150367 m n)). Qed.
Lemma lem150375 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (x = (NUMERAL 0)) = ((term11 n x m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0)))).
Proof. exact (prop_ext (fun h2 : x = (NUMERAL 0) => @lem150374 m n x h1) (fun h2 : (term11 n x m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0))) => @lem149275 x h1)). Qed.
Lemma lem150376 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term11 n x m) = ((m = (NUMERAL 0)) = (n = (NUMERAL 0))).
Proof. exact (EQ_MP (@lem150375 m n x h1) (@lem149275 x h1)). Qed.
Lemma lem150377 (x : nat) (m : nat) (n : nat) : term30 x m n.
Proof. exact (fun h0 : x = (NUMERAL 0) => @lem150376 m n x h0). Qed.
Lemma lem150378 (x : nat) (m : nat) (n : nat) : term33 x m n.
Proof. exact (conj (@lem150377 x m n) (@lem150373 x m n)). Qed.
Lemma lem150379 (x : nat) (m : nat) (n : nat) : (term11 n x m) = (term14 x m n).
Proof. exact (EQ_MP (@lem149274 x m n) (@lem150378 x m n)). Qed.
Lemma lem150380 (x : nat) (m : nat) (n : nat) : ((Nat.pow x m) = (Nat.pow x n)) = (term14 x m n).
Proof. exact (EQ_MP (@lem149256 x m n) (@lem150379 x m n)). Qed.
Lemma lem150385 (x : nat) (m : nat) : term186 x m.
Proof. exact (fun n : nat => @lem150380 x m n). Qed.
Lemma lem150390 (x : nat) : term187 x.
Proof. exact (fun m : nat => @lem150385 x m). Qed.
Lemma lem150395 : term188.
Proof. exact (fun x : nat => @lem150390 x). Qed.
