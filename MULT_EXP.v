Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_EXP_term_abbrevs.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm86199_spec.
Lemma lem88198 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem88199 : term1.
Proof. exact (@lem88198 term2). Qed.
Lemma lem88200 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem88201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem88202 : term5 = term6.
Proof. exact (MK_COMB (@lem88201) (@lem88200)). Qed.
Lemma lem88203 (p : nat) : (term7 p) = (term8 p).
Proof. exact (eq_refl (term7 p)). Qed.
Lemma lem88204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem88205 (p : nat) : (term9 p) = (term10 p).
Proof. exact (MK_COMB (@lem88204) (@lem88203 p)). Qed.
Lemma lem88206 (p : nat) : (term11 p) = (term12 p).
Proof. exact (eq_refl (term11 p)). Qed.
Lemma lem88207 (p : nat) : (term13 p) = (term14 p).
Proof. exact (MK_COMB (@lem88205 p) (@lem88206 p)). Qed.
Lemma lem88208 : term15 = term16.
Proof. exact (fun_ext (fun p : nat => @lem88207 p)). Qed.
Lemma lem88209 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88210 : term17 = term18.
Proof. exact (MK_COMB (@lem88209) (@lem88208)). Qed.
Lemma lem88211 : term19 = term20.
Proof. exact (MK_COMB (@lem88202) (@lem88210)). Qed.
Lemma lem88212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem88213 : term21 = term22.
Proof. exact (MK_COMB (@lem88212) (@lem88211)). Qed.
Lemma lem88214 (p : nat) : (term7 p) = (term8 p).
Proof. exact (eq_refl (term7 p)). Qed.
Lemma lem88215 : term23 = term2.
Proof. exact (fun_ext (fun p : nat => @lem88214 p)). Qed.
Lemma lem88216 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88217 : term24 = term25.
Proof. exact (MK_COMB (@lem88216) (@lem88215)). Qed.
Lemma lem88218 : term1 = term26.
Proof. exact (MK_COMB (@lem88213) (@lem88217)). Qed.
Lemma lem88219 : term26.
Proof. exact (EQ_MP (@lem88218) (@lem88199)). Qed.
Lemma lem88220 (p : nat) (h1 : term8 p) : term8 p.
Proof. exact (h1). Qed.
Lemma lem88225 : term27.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem88226 : term28.
Proof. exact (proj2 (@lem88225)). Qed.
Lemma lem88247 : term29.
Proof. exact (proj1 (@lem88226)). Qed.
Lemma lem88248 (n : nat) : term30 n.
Proof. exact (@lem88247 n). Qed.
Lemma lem88249 (n : nat) : (term30 n) = ((term31 n) = n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem88266 : term32.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem88267 (m : nat) : term33 m.
Proof. exact (@lem88266 m). Qed.
Lemma lem88268 (m : nat) : (term33 m) = ((term34 m) = term35).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem88281 (m : nat) : (term34 m) = term35.
Proof. exact (EQ_MP (@lem88268 m) (@lem88267 m)). Qed.
Lemma lem88282 (m : nat) (n : nat) : (term36 m n) = term35.
Proof. exact (@lem88281 (Nat.mul m n)). Qed.
Lemma lem88283 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem88284 (m : nat) (n : nat) : (term37 m n) = term38.
Proof. exact (MK_COMB (@lem88283) (@lem88282 m n)). Qed.
Lemma lem88289 (m : nat) : (term34 m) = term35.
Proof. exact (EQ_MP (@lem88268 m) (@lem88267 m)). Qed.
Lemma lem88290 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem88291 (m : nat) : (term39 m) = term40.
Proof. exact (MK_COMB (@lem88290) (@lem88289 m)). Qed.
Lemma lem88293 (m : nat) : (term34 m) = term35.
Proof. exact (EQ_MP (@lem88268 m) (@lem88267 m)). Qed.
Lemma lem88294 (n : nat) : (term34 n) = term35.
Proof. exact (@lem88293 n). Qed.
Lemma lem88295 (m : nat) (n : nat) : (term41 m n) = term42.
Proof. exact (MK_COMB (@lem88291 m) (@lem88294 n)). Qed.
Lemma lem88297 (n : nat) : (term31 n) = n.
Proof. exact (EQ_MP (@lem88249 n) (@lem88248 n)). Qed.
Lemma lem88298 : term42 = term35.
Proof. exact (@lem88297 term35). Qed.
Lemma lem88299 (m : nat) (n : nat) : (term41 m n) = term35.
Proof. exact (TRANS (@lem88295 m n) (@lem88298)). Qed.
Lemma lem88300 (m : nat) (n : nat) : ((term36 m n) = (term41 m n)) = (term35 = term35).
Proof. exact (MK_COMB (@lem88284 m n) (@lem88299 m n)). Qed.
Lemma lem88302 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem88303 (x : nat) : (x = x) = True.
Proof. exact (@lem88302 nat x). Qed.
Lemma lem88304 : (term35 = term35) = True.
Proof. exact (@lem88303 term35). Qed.
Lemma lem88305 (m : nat) (n : nat) : ((term36 m n) = (term41 m n)) = True.
Proof. exact (TRANS (@lem88300 m n) (@lem88304)). Qed.
Lemma lem88306 (m : nat) : (term43 m) = term44.
Proof. exact (fun_ext (fun n : nat => @lem88305 m n)). Qed.
Lemma lem88307 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88308 (m : nat) : (term45 m) = term46.
Proof. exact (MK_COMB (@lem88307) (@lem88306 m)). Qed.
Lemma lem88310 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem88311 (t : Prop) : (term48 t) = t.
Proof. exact (@lem88310 nat t). Qed.
Lemma lem88312 : term46 = True.
Proof. exact (@lem88311 True). Qed.
Lemma lem88313 (m : nat) : (term45 m) = True.
Proof. exact (TRANS (@lem88308 m) (@lem88312)). Qed.
Lemma lem88314 : term49 = term44.
Proof. exact (fun_ext (fun m : nat => @lem88313 m)). Qed.
Lemma lem88315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88316 : term4 = term46.
Proof. exact (MK_COMB (@lem88315) (@lem88314)). Qed.
Lemma lem88318 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem88319 (t : Prop) : (term48 t) = t.
Proof. exact (@lem88318 nat t). Qed.
Lemma lem88320 : term46 = True.
Proof. exact (@lem88319 True). Qed.
Lemma lem88321 : term4 = True.
Proof. exact (TRANS (@lem88316) (@lem88320)). Qed.
Lemma lem88322 : True = term4.
Proof. exact (SYM (@lem88321)). Qed.
Lemma lem88323 : term4.
Proof. exact (EQ_MP (@lem88322) (@lem0)). Qed.
Lemma lem88324 (n : nat) (m : nat) (p : nat) : term50 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem88362 : term51.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem88363 (m : nat) : term52 m.
Proof. exact (@lem88362 m). Qed.
Lemma lem88364 (m : nat) : (term52 m) = (term53 m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem88365 (m : nat) : term53 m.
Proof. exact (EQ_MP (@lem88364 m) (@lem88363 m)). Qed.
Lemma lem88366 (m : nat) (n : nat) : term54 m n.
Proof. exact (@lem88365 m n). Qed.
Lemma lem88367 (m : nat) (n : nat) : (term54 m n) = ((term55 m n) = (term56 m n)).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem88373 (m : nat) (p : nat) (h1 : term8 p) : term57 p m.
Proof. exact (@lem88220 p h1 m). Qed.
Lemma lem88374 (m : nat) (p : nat) : (term57 p m) = (term58 m p).
Proof. exact (eq_refl (term57 p m)). Qed.
Lemma lem88375 (m : nat) (p : nat) (h1 : term8 p) : term58 m p.
Proof. exact (EQ_MP (@lem88374 m p) (@lem88373 m p h1)). Qed.
Lemma lem88376 (m : nat) (n : nat) (p : nat) (h1 : term8 p) : term59 m p n.
Proof. exact (@lem88375 m p h1 n). Qed.
Lemma lem88377 (m : nat) (n : nat) (p : nat) : (term59 m p n) = ((term60 m n p) = (term61 m n p)).
Proof. exact (eq_refl (term59 m p n)). Qed.
Lemma lem88390 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (EQ_MP (@lem88367 m n) (@lem88366 m n)). Qed.
Lemma lem88391 (m : nat) (n : nat) (p : nat) : (term62 m n p) = (term63 m n p).
Proof. exact (@lem88390 (Nat.mul m n) p). Qed.
Lemma lem88393 (m : nat) (n : nat) (p : nat) : (term64 m n p) = (term65 m n p).
Proof. exact (proj1 (@lem88324 n m p)). Qed.
Lemma lem88394 (m : nat) (n : nat) (p : nat) : (term63 m n p) = (term66 m n p).
Proof. exact (@lem88393 m n (term60 m n p)). Qed.
Lemma lem88401 (m : nat) (n : nat) (p : nat) : (term62 m n p) = (term66 m n p).
Proof. exact (TRANS (@lem88391 m n p) (@lem88394 m n p)). Qed.
Lemma lem88406 (m : nat) (n : nat) (p : nat) (h1 : term8 p) : (term60 m n p) = (term61 m n p).
Proof. exact (EQ_MP (@lem88377 m n p) (@lem88376 m n p h1)). Qed.
Lemma lem88410 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem88411 (m : nat) (n : nat) (p : nat) (h1 : term8 p) : (term67 m n p) = (term68 m n p).
Proof. exact (MK_COMB (@lem88410 n) (@lem88406 m n p h1)). Qed.
Lemma lem88418 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem88419 (m : nat) (n : nat) (p : nat) (h1 : term8 p) : (term66 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem88418 m) (@lem88411 m n p h1)). Qed.
Lemma lem88426 (m : nat) (n : nat) (p : nat) (h1 : term8 p) : (term62 m n p) = (term69 m n p).
Proof. exact (TRANS (@lem88401 m n p) (@lem88419 m n p h1)). Qed.
Lemma lem88427 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem88428 (m : nat) (n : nat) (p : nat) (h1 : term8 p) : (term70 m n p) = (term71 m n p).
Proof. exact (MK_COMB (@lem88427) (@lem88426 m n p h1)). Qed.
Lemma lem88433 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (EQ_MP (@lem88367 m n) (@lem88366 m n)). Qed.
Lemma lem88434 (m : nat) (p : nat) : (term55 m p) = (term56 m p).
Proof. exact (@lem88433 m p). Qed.
Lemma lem88438 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem88439 (m : nat) (p : nat) : (term72 m p) = (term73 m p).
Proof. exact (MK_COMB (@lem88438) (@lem88434 m p)). Qed.
Lemma lem88441 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (EQ_MP (@lem88367 m n) (@lem88366 m n)). Qed.
Lemma lem88442 (n : nat) (p : nat) : (term55 n p) = (term56 n p).
Proof. exact (@lem88441 n p). Qed.
Lemma lem88446 (m : nat) (n : nat) (p : nat) : (term74 m n p) = (term75 m n p).
Proof. exact (MK_COMB (@lem88439 m p) (@lem88442 n p)). Qed.
Lemma lem88448 (m : nat) (n : nat) (p : nat) : (term64 m n p) = (term65 m n p).
Proof. exact (proj1 (@lem88324 n m p)). Qed.
Lemma lem88449 (m : nat) (n : nat) (p : nat) : (term75 m n p) = (term76 m n p).
Proof. exact (@lem88448 m (Nat.pow m p) (term56 n p)). Qed.
Lemma lem88457 (n : nat) (m : nat) (p : nat) : (term65 m n p) = (term65 n m p).
Proof. exact (proj2 (@lem88324 n m p)). Qed.
Lemma lem88458 (m : nat) (n : nat) (p : nat) : (term77 m n p) = (term68 m n p).
Proof. exact (@lem88457 n (Nat.pow m p) (Nat.pow n p)). Qed.
Lemma lem88468 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem88469 (m : nat) (n : nat) (p : nat) : (term76 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem88468 m) (@lem88458 m n p)). Qed.
Lemma lem88476 (m : nat) (n : nat) (p : nat) : (term75 m n p) = (term69 m n p).
Proof. exact (TRANS (@lem88449 m n p) (@lem88469 m n p)). Qed.
Lemma lem88477 (m : nat) (n : nat) (p : nat) : (term74 m n p) = (term69 m n p).
Proof. exact (TRANS (@lem88446 m n p) (@lem88476 m n p)). Qed.
Lemma lem88478 (m : nat) (n : nat) (p : nat) (h1 : term8 p) : ((term62 m n p) = (term74 m n p)) = ((term69 m n p) = (term69 m n p)).
Proof. exact (MK_COMB (@lem88428 m n p h1) (@lem88477 m n p)). Qed.
Lemma lem88480 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem88481 (x : nat) : (x = x) = True.
Proof. exact (@lem88480 nat x). Qed.
Lemma lem88482 (m : nat) (n : nat) (p : nat) : ((term69 m n p) = (term69 m n p)) = True.
Proof. exact (@lem88481 (term69 m n p)). Qed.
Lemma lem88483 (m : nat) (n : nat) (p : nat) (h1 : term8 p) : ((term62 m n p) = (term74 m n p)) = True.
Proof. exact (TRANS (@lem88478 m n p h1) (@lem88482 m n p)). Qed.
Lemma lem88484 (m : nat) (p : nat) (h1 : term8 p) : (term78 m p) = term44.
Proof. exact (fun_ext (fun n : nat => @lem88483 m n p h1)). Qed.
Lemma lem88485 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88486 (m : nat) (p : nat) (h1 : term8 p) : (term79 m p) = term46.
Proof. exact (MK_COMB (@lem88485) (@lem88484 m p h1)). Qed.
Lemma lem88488 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem88489 (t : Prop) : (term48 t) = t.
Proof. exact (@lem88488 nat t). Qed.
Lemma lem88490 : term46 = True.
Proof. exact (@lem88489 True). Qed.
Lemma lem88491 (m : nat) (p : nat) (h1 : term8 p) : (term79 m p) = True.
Proof. exact (TRANS (@lem88486 m p h1) (@lem88490)). Qed.
Lemma lem88492 (p : nat) (h1 : term8 p) : (term80 p) = term44.
Proof. exact (fun_ext (fun m : nat => @lem88491 m p h1)). Qed.
Lemma lem88493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88494 (p : nat) (h1 : term8 p) : (term12 p) = term46.
Proof. exact (MK_COMB (@lem88493) (@lem88492 p h1)). Qed.
Lemma lem88496 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem88497 (t : Prop) : (term48 t) = t.
Proof. exact (@lem88496 nat t). Qed.
Lemma lem88498 : term46 = True.
Proof. exact (@lem88497 True). Qed.
Lemma lem88499 (p : nat) (h1 : term8 p) : (term12 p) = True.
Proof. exact (TRANS (@lem88494 p h1) (@lem88498)). Qed.
Lemma lem88500 (p : nat) (h1 : term8 p) : True = (term12 p).
Proof. exact (SYM (@lem88499 p h1)). Qed.
Lemma lem88501 (p : nat) (h1 : term8 p) : term12 p.
Proof. exact (EQ_MP (@lem88500 p h1) (@lem0)). Qed.
Lemma lem88502 (p : nat) : term14 p.
Proof. exact (fun h0 : term8 p => @lem88501 p h0). Qed.
Lemma lem88507 : term18.
Proof. exact (fun p : nat => @lem88502 p). Qed.
Lemma lem88508 : term20.
Proof. exact (conj (@lem88323) (@lem88507)). Qed.
Lemma lem88509 : term25.
Proof. exact (@lem88219 (@lem88508)). Qed.
