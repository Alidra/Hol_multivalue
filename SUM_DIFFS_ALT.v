Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_DIFFS_ALT_term_abbrevs.
Require Import REAL_NEG_SUB_spec.
Require Import SUM_DIFFS_spec.
Require Import SUM_NEG_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1361604_spec.
Require Import thm1362040_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem7235164 (f : nat -> real) (m : nat) : term0 f m.
Proof. exact (@lem7235163 f m). Qed.
Lemma lem7235165 (m : nat) (f : nat -> real) : (term0 f m) = (term1 m f).
Proof. exact (eq_refl (term0 f m)). Qed.
Lemma lem7235166 (m : nat) (f : nat -> real) : term1 m f.
Proof. exact (EQ_MP (@lem7235165 m f) (@lem7235164 f m)). Qed.
Lemma lem7235167 (m : nat) (f : nat -> real) (n : nat) : term2 m f n.
Proof. exact (@lem7235166 m f n). Qed.
Lemma lem7235168 (m : nat) (f : nat -> real) (n : nat) : (term2 m f n) = ((term3 m n f) = (term4 m f n)).
Proof. exact (eq_refl (term2 m f n)). Qed.
Lemma lem7235170 {_132004 : Type'} (f : _132004 -> real) : term5 _132004 f.
Proof. exact (@lem7070827 _132004 f). Qed.
Lemma lem7235171 {_132004 : Type'} (f : _132004 -> real) : (term5 _132004 f) = (term6 _132004 f).
Proof. exact (eq_refl (term5 _132004 f)). Qed.
Lemma lem7235172 {_132004 : Type'} (f : _132004 -> real) : term6 _132004 f.
Proof. exact (EQ_MP (@lem7235171 _132004 f) (@lem7235170 _132004 f)). Qed.
Lemma lem7235173 {_132004 : Type'} (f : _132004 -> real) (s : _132004 -> Prop) : term7 _132004 f s.
Proof. exact (@lem7235172 _132004 f s). Qed.
Lemma lem7235174 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term7 _132004 f s) = ((term8 _132004 s f) = (term9 _132004 s f)).
Proof. exact (eq_refl (term7 _132004 f s)). Qed.
Lemma lem7235178 (y : real) (x : real) (h1 : (term10 x y) = (real_sub y x)) : (term10 x y) = (real_sub y x).
Proof. exact (h1). Qed.
Lemma lem7235179 (y : real) (x : real) (h1 : (term10 x y) = (real_sub y x)) : (real_sub y x) = (term10 x y).
Proof. exact (SYM (@lem7235178 y x h1)). Qed.
Lemma lem7235180 (x : real) (y : real) (h1 : (real_sub y x) = (term10 x y)) : (real_sub y x) = (term10 x y).
Proof. exact (h1). Qed.
Lemma lem7235181 (x : real) (y : real) (h1 : (real_sub y x) = (term10 x y)) : (term10 x y) = (real_sub y x).
Proof. exact (SYM (@lem7235180 x y h1)). Qed.
Lemma lem7235182 (x : real) (y : real) : ((term10 x y) = (real_sub y x)) = ((real_sub y x) = (term10 x y)).
Proof. exact (prop_ext (fun h1 : (term10 x y) = (real_sub y x) => @lem7235179 y x h1) (fun h1 : (real_sub y x) = (term10 x y) => @lem7235181 x y h1)). Qed.
Lemma lem7235183 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem7235182 x y)). Qed.
Lemma lem7235184 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7235185 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem7235184) (@lem7235183 x)). Qed.
Lemma lem7235186 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem7235185 x)). Qed.
Lemma lem7235187 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7235188 : term17 = term18.
Proof. exact (MK_COMB (@lem7235187) (@lem7235186)). Qed.
Lemma lem7235189 : term18.
Proof. exact (EQ_MP (@lem7235188) (@lem1374337)). Qed.
Lemma lem7235190 (x : real) : term19 x.
Proof. exact (@lem7235189 x). Qed.
Lemma lem7235191 (x : real) : (term19 x) = (term14 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem7235192 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem7235191 x) (@lem7235190 x)). Qed.
Lemma lem7235193 (x : real) (y : real) : term20 x y.
Proof. exact (@lem7235192 x y). Qed.
Lemma lem7235194 (x : real) (y : real) : (term20 x y) = ((real_sub y x) = (term10 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem7235199 (x : real) (y : real) : (real_sub y x) = (term10 x y).
Proof. exact (EQ_MP (@lem7235194 x y) (@lem7235193 x y)). Qed.
Lemma lem7235200 (f : nat -> real) (k : nat) : (term21 f k) = (term22 f k).
Proof. exact (@lem7235199 (f k) (term23 f k)). Qed.
Lemma lem7235201 (f : nat -> real) : (term24 f) = (term25 f).
Proof. exact (fun_ext (fun k : nat => @lem7235200 f k)). Qed.
Lemma lem7235202 (m : nat) (n : nat) : (term26 m n) = (term26 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem7235203 (m : nat) (n : nat) (f : nat -> real) : (term27 m n f) = (term28 m n f).
Proof. exact (MK_COMB (@lem7235202 m n) (@lem7235201 f)). Qed.
Lemma lem7235204 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7235205 (m : nat) (n : nat) (f : nat -> real) : (term29 m n f) = (term30 m n f).
Proof. exact (MK_COMB (@lem7235204) (@lem7235203 m n f)). Qed.
Lemma lem7235207 (x : real) (y : real) : (real_sub y x) = (term10 x y).
Proof. exact (EQ_MP (@lem7235194 x y) (@lem7235193 x y)). Qed.
Lemma lem7235208 (m : nat) (f : nat -> real) (n : nat) : (term31 n f m) = (term32 m f n).
Proof. exact (@lem7235207 (f m) (term23 f n)). Qed.
Lemma lem7235209 (m : nat) (n : nat) : (term33 m n) = (term33 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem7235210 (m : nat) (f : nat -> real) (n : nat) : (term34 n f m) = (term35 m f n).
Proof. exact (MK_COMB (@lem7235209 m n) (@lem7235208 m f n)). Qed.
Lemma lem7235211 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem7235212 (m : nat) (f : nat -> real) (n : nat) : (term37 n f m) = (term38 m f n).
Proof. exact (MK_COMB (@lem7235210 m f n) (@lem7235211)). Qed.
Lemma lem7235213 (m : nat) (f : nat -> real) (n : nat) : ((term27 m n f) = (term37 n f m)) = ((term28 m n f) = (term38 m f n)).
Proof. exact (MK_COMB (@lem7235205 m n f) (@lem7235212 m f n)). Qed.
Lemma lem7235214 (n : nat) (f : nat -> real) (m : nat) : ((term28 m n f) = (term38 m f n)) = ((term27 m n f) = (term37 n f m)).
Proof. exact (SYM (@lem7235213 m f n)). Qed.
Lemma lem7235218 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term8 _132004 s f) = (term9 _132004 s f).
Proof. exact (EQ_MP (@lem7235174 _132004 s f) (@lem7235173 _132004 f s)). Qed.
Lemma lem7235219 (s : nat -> Prop) (f : nat -> real) : (term39 s f) = (term40 s f).
Proof. exact (@lem7235218 nat s f). Qed.
Lemma lem7235220 (m : nat) (n : nat) (f : nat -> real) : (term41 m n f) = (term42 m n f).
Proof. exact (@lem7235219 (dotdot m n) (term43 f)). Qed.
Lemma lem7235221 (f : nat -> real) (k : nat) : (term44 f k) = (term45 f k).
Proof. exact (eq_refl (term44 f k)). Qed.
Lemma lem7235222 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7235223 (f : nat -> real) (k : nat) : (term46 f k) = (term22 f k).
Proof. exact (MK_COMB (@lem7235222) (@lem7235221 f k)). Qed.
Lemma lem7235224 (f : nat -> real) : (term47 f) = (term25 f).
Proof. exact (fun_ext (fun k : nat => @lem7235223 f k)). Qed.
Lemma lem7235225 (m : nat) (n : nat) : (term26 m n) = (term26 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem7235226 (m : nat) (n : nat) (f : nat -> real) : (term41 m n f) = (term28 m n f).
Proof. exact (MK_COMB (@lem7235225 m n) (@lem7235224 f)). Qed.
Lemma lem7235227 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7235228 (m : nat) (n : nat) (f : nat -> real) : (term48 m n f) = (term30 m n f).
Proof. exact (MK_COMB (@lem7235227) (@lem7235226 m n f)). Qed.
Lemma lem7235229 (m : nat) (n : nat) (f : nat -> real) : (term42 m n f) = (term42 m n f).
Proof. exact (eq_refl (term42 m n f)). Qed.
Lemma lem7235230 (m : nat) (n : nat) (f : nat -> real) : ((term41 m n f) = (term42 m n f)) = ((term28 m n f) = (term42 m n f)).
Proof. exact (MK_COMB (@lem7235228 m n f) (@lem7235229 m n f)). Qed.
Lemma lem7235231 (m : nat) (n : nat) (f : nat -> real) : (term28 m n f) = (term42 m n f).
Proof. exact (EQ_MP (@lem7235230 m n f) (@lem7235220 m n f)). Qed.
Lemma lem7235233 (m : nat) (f : nat -> real) (n : nat) : (term3 m n f) = (term4 m f n).
Proof. exact (EQ_MP (@lem7235168 m f n) (@lem7235167 m f n)). Qed.
Lemma lem7235267 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7235268 (m : nat) (f : nat -> real) (n : nat) : (term42 m n f) = (term49 m f n).
Proof. exact (MK_COMB (@lem7235267) (@lem7235233 m f n)). Qed.
Lemma lem7235302 (m : nat) (f : nat -> real) (n : nat) : (term28 m n f) = (term49 m f n).
Proof. exact (TRANS (@lem7235231 m n f) (@lem7235268 m f n)). Qed.
Lemma lem7235303 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7235304 (m : nat) (f : nat -> real) (n : nat) : (term30 m n f) = (term50 m f n).
Proof. exact (MK_COMB (@lem7235303) (@lem7235302 m f n)). Qed.
Lemma lem7235371 (m : nat) (f : nat -> real) (n : nat) : (term38 m f n) = (term38 m f n).
Proof. exact (eq_refl (term38 m f n)). Qed.
Lemma lem7235372 (m : nat) (f : nat -> real) (n : nat) : ((term28 m n f) = (term38 m f n)) = ((term49 m f n) = (term38 m f n)).
Proof. exact (MK_COMB (@lem7235304 m f n) (@lem7235371 m f n)). Qed.
Lemma lem7235441 (m : nat) (f : nat -> real) (n : nat) : ((term49 m f n) = (term38 m f n)) = ((term28 m n f) = (term38 m f n)).
Proof. exact (SYM (@lem7235372 m f n)). Qed.
Lemma lem7235442 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term51 _476 _475 _474 _477) = (term52 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem7235443 (_474 : real) (_475 : Prop) (m : nat) (f : nat -> real) (n : nat) (_477 : real) : (term53 m f n _475 _474 _477) = (term54 _474 _475 m f n _477).
Proof. exact (@lem7235442 _474 _475 (term55 m f n) _477). Qed.
Lemma lem7235444 (m : nat) (f : nat -> real) (n : nat) : (term56 m f n) = (term57 m f n).
Proof. exact (@lem7235443 (term58 m f n) (Peano.le m n) m f n term36). Qed.
Lemma lem7235445 (m : nat) (f : nat -> real) (n : nat) : (term59 m f n) = (term60 = (term38 m f n)).
Proof. exact (eq_refl (term59 m f n)). Qed.
Lemma lem7235446 (m : nat) (n : nat) : (term61 m n) = (term61 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem7235447 (m : nat) (f : nat -> real) (n : nat) : (term62 m f n) = (term63 m f n).
Proof. exact (MK_COMB (@lem7235446 m n) (@lem7235445 m f n)). Qed.
Lemma lem7235448 (m : nat) (f : nat -> real) (n : nat) : (term64 m f n) = ((term32 m f n) = (term38 m f n)).
Proof. exact (eq_refl (term64 m f n)). Qed.
Lemma lem7235449 (m : nat) (n : nat) : (term65 m n) = (term65 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem7235450 (m : nat) (f : nat -> real) (n : nat) : (term66 m f n) = (term67 m f n).
Proof. exact (MK_COMB (@lem7235449 m n) (@lem7235448 m f n)). Qed.
Lemma lem7235451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7235452 (m : nat) (f : nat -> real) (n : nat) : (term68 m f n) = (term69 m f n).
Proof. exact (MK_COMB (@lem7235451) (@lem7235450 m f n)). Qed.
Lemma lem7235453 (m : nat) (f : nat -> real) (n : nat) : (term57 m f n) = (term70 m f n).
Proof. exact (MK_COMB (@lem7235452 m f n) (@lem7235447 m f n)). Qed.
Lemma lem7235454 (m : nat) (f : nat -> real) (n : nat) : (term56 m f n) = ((term49 m f n) = (term38 m f n)).
Proof. exact (eq_refl (term56 m f n)). Qed.
Lemma lem7235455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7235456 (m : nat) (f : nat -> real) (n : nat) : (term71 m f n) = (term72 m f n).
Proof. exact (MK_COMB (@lem7235455) (@lem7235454 m f n)). Qed.
Lemma lem7235457 (m : nat) (f : nat -> real) (n : nat) : ((term56 m f n) = (term57 m f n)) = (((term49 m f n) = (term38 m f n)) = (term70 m f n)).
Proof. exact (MK_COMB (@lem7235456 m f n) (@lem7235453 m f n)). Qed.
Lemma lem7235458 (m : nat) (f : nat -> real) (n : nat) : ((term49 m f n) = (term38 m f n)) = (term70 m f n).
Proof. exact (EQ_MP (@lem7235457 m f n) (@lem7235444 m f n)). Qed.
Lemma lem7235459 (m : nat) (f : nat -> real) (n : nat) : (term70 m f n) = ((term49 m f n) = (term38 m f n)).
Proof. exact (SYM (@lem7235458 m f n)). Qed.
Lemma lem7235460 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7235461 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem7235462 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem7235461 m n) (@lem7235460 m n h1)). Qed.
Lemma lem7235463 (m : nat) (f : nat -> real) (n : nat) : (term73 m f n) = (term73 m f n).
Proof. exact (eq_refl (term73 m f n)). Qed.
Lemma lem7235464 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term74 f m n) = (term75 m f n).
Proof. exact (MK_COMB (@lem7235463 m f n) (@lem7235462 m n h1)). Qed.
Lemma lem7235465 (m : nat) (f : nat -> real) (n : nat) : (term75 m f n) = ((term32 m f n) = (term76 m f n)).
Proof. exact (eq_refl (term75 m f n)). Qed.
Lemma lem7235466 (f : nat -> real) (m : nat) (n : nat) : (term77 f m n) = (term77 f m n).
Proof. exact (eq_refl (term77 f m n)). Qed.
Lemma lem7235467 (m : nat) (f : nat -> real) (n : nat) : ((term74 f m n) = (term75 m f n)) = ((term74 f m n) = ((term32 m f n) = (term76 m f n))).
Proof. exact (MK_COMB (@lem7235466 f m n) (@lem7235465 m f n)). Qed.
Lemma lem7235468 (m : nat) (f : nat -> real) (n : nat) : (term74 f m n) = ((term32 m f n) = (term38 m f n)).
Proof. exact (eq_refl (term74 f m n)). Qed.
Lemma lem7235469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7235470 (m : nat) (f : nat -> real) (n : nat) : (term77 f m n) = (term78 m f n).
Proof. exact (MK_COMB (@lem7235469) (@lem7235468 m f n)). Qed.
Lemma lem7235471 (m : nat) (f : nat -> real) (n : nat) : ((term32 m f n) = (term76 m f n)) = ((term32 m f n) = (term76 m f n)).
Proof. exact (eq_refl ((term32 m f n) = (term76 m f n))). Qed.
Lemma lem7235472 (m : nat) (f : nat -> real) (n : nat) : ((term74 f m n) = ((term32 m f n) = (term76 m f n))) = (((term32 m f n) = (term38 m f n)) = ((term32 m f n) = (term76 m f n))).
Proof. exact (MK_COMB (@lem7235470 m f n) (@lem7235471 m f n)). Qed.
Lemma lem7235473 (m : nat) (f : nat -> real) (n : nat) : ((term74 f m n) = (term75 m f n)) = (((term32 m f n) = (term38 m f n)) = ((term32 m f n) = (term76 m f n))).
Proof. exact (TRANS (@lem7235467 m f n) (@lem7235472 m f n)). Qed.
Lemma lem7235474 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term32 m f n) = (term38 m f n)) = ((term32 m f n) = (term76 m f n)).
Proof. exact (EQ_MP (@lem7235473 m f n) (@lem7235464 f m n h1)). Qed.
Lemma lem7235475 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term32 m f n) = (term76 m f n)) = ((term32 m f n) = (term38 m f n)).
Proof. exact (SYM (@lem7235474 f m n h1)). Qed.
Lemma lem7235476 (m : nat) (n : nat) (h1 : term79 m n) : term79 m n.
Proof. exact (h1). Qed.
Lemma lem7235477 (m : nat) (n : nat) : term80 m n.
Proof. exact (@lem82 (Peano.le m n)). Qed.
Lemma lem7235478 (m : nat) (n : nat) (h1 : term79 m n) : (Peano.le m n) = False.
Proof. exact (@lem7235477 m n (@lem7235476 m n h1)). Qed.
Lemma lem7235479 (m : nat) (f : nat -> real) (n : nat) : (term81 m f n) = (term81 m f n).
Proof. exact (eq_refl (term81 m f n)). Qed.
Lemma lem7235480 (f : nat -> real) (m : nat) (n : nat) (h1 : term79 m n) : (term82 f m n) = (term83 m f n).
Proof. exact (MK_COMB (@lem7235479 m f n) (@lem7235478 m n h1)). Qed.
Lemma lem7235481 (m : nat) (f : nat -> real) (n : nat) : (term83 m f n) = (term60 = (term84 m f n)).
Proof. exact (eq_refl (term83 m f n)). Qed.
Lemma lem7235482 (f : nat -> real) (m : nat) (n : nat) : (term85 f m n) = (term85 f m n).
Proof. exact (eq_refl (term85 f m n)). Qed.
Lemma lem7235483 (m : nat) (f : nat -> real) (n : nat) : ((term82 f m n) = (term83 m f n)) = ((term82 f m n) = (term60 = (term84 m f n))).
Proof. exact (MK_COMB (@lem7235482 f m n) (@lem7235481 m f n)). Qed.
Lemma lem7235484 (m : nat) (f : nat -> real) (n : nat) : (term82 f m n) = (term60 = (term38 m f n)).
Proof. exact (eq_refl (term82 f m n)). Qed.
Lemma lem7235485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7235486 (m : nat) (f : nat -> real) (n : nat) : (term85 f m n) = (term86 m f n).
Proof. exact (MK_COMB (@lem7235485) (@lem7235484 m f n)). Qed.
Lemma lem7235487 (m : nat) (f : nat -> real) (n : nat) : (term60 = (term84 m f n)) = (term60 = (term84 m f n)).
Proof. exact (eq_refl (term60 = (term84 m f n))). Qed.
Lemma lem7235488 (m : nat) (f : nat -> real) (n : nat) : ((term82 f m n) = (term60 = (term84 m f n))) = ((term60 = (term38 m f n)) = (term60 = (term84 m f n))).
Proof. exact (MK_COMB (@lem7235486 m f n) (@lem7235487 m f n)). Qed.
Lemma lem7235489 (m : nat) (f : nat -> real) (n : nat) : ((term82 f m n) = (term83 m f n)) = ((term60 = (term38 m f n)) = (term60 = (term84 m f n))).
Proof. exact (TRANS (@lem7235483 m f n) (@lem7235488 m f n)). Qed.
Lemma lem7235490 (f : nat -> real) (m : nat) (n : nat) (h1 : term79 m n) : (term60 = (term38 m f n)) = (term60 = (term84 m f n)).
Proof. exact (EQ_MP (@lem7235489 m f n) (@lem7235480 f m n h1)). Qed.
Lemma lem7235491 (f : nat -> real) (m : nat) (n : nat) (h1 : term79 m n) : (term60 = (term84 m f n)) = (term60 = (term38 m f n)).
Proof. exact (SYM (@lem7235490 f m n h1)). Qed.
Lemma lem7235492 (x : real) : term87 x.
Proof. exact (@lem1374337 x). Qed.
Lemma lem7235493 (x : real) : (term87 x) = (term13 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem7235494 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem7235493 x) (@lem7235492 x)). Qed.
Lemma lem7235495 (x : real) (y : real) : term88 x y.
Proof. exact (@lem7235494 x y). Qed.
Lemma lem7235496 (y : real) (x : real) : (term88 x y) = ((term10 x y) = (real_sub y x)).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem7235503 (y : real) (x : real) : (term10 x y) = (real_sub y x).
Proof. exact (EQ_MP (@lem7235496 y x) (@lem7235495 x y)). Qed.
Lemma lem7235504 (n : nat) (f : nat -> real) (m : nat) : (term32 m f n) = (term31 n f m).
Proof. exact (@lem7235503 (term23 f n) (f m)). Qed.
Lemma lem7235505 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7235506 (n : nat) (f : nat -> real) (m : nat) : (term89 m f n) = (term90 n f m).
Proof. exact (MK_COMB (@lem7235505) (@lem7235504 n f m)). Qed.
Lemma lem7235508 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7235509 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7235508 real t2 t1). Qed.
Lemma lem7235510 (m : nat) (f : nat -> real) (n : nat) : (term76 m f n) = (term32 m f n).
Proof. exact (@lem7235509 term36 (term32 m f n)). Qed.
Lemma lem7235512 (y : real) (x : real) : (term10 x y) = (real_sub y x).
Proof. exact (EQ_MP (@lem7235496 y x) (@lem7235495 x y)). Qed.
Lemma lem7235513 (n : nat) (f : nat -> real) (m : nat) : (term32 m f n) = (term31 n f m).
Proof. exact (@lem7235512 (term23 f n) (f m)). Qed.
Lemma lem7235514 (n : nat) (f : nat -> real) (m : nat) : (term76 m f n) = (term31 n f m).
Proof. exact (TRANS (@lem7235510 m f n) (@lem7235513 n f m)). Qed.
Lemma lem7235515 (n : nat) (f : nat -> real) (m : nat) : ((term32 m f n) = (term76 m f n)) = ((term31 n f m) = (term31 n f m)).
Proof. exact (MK_COMB (@lem7235506 n f m) (@lem7235514 n f m)). Qed.
Lemma lem7235517 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7235518 (x : real) : (x = x) = True.
Proof. exact (@lem7235517 real x). Qed.
Lemma lem7235519 (n : nat) (f : nat -> real) (m : nat) : ((term31 n f m) = (term31 n f m)) = True.
Proof. exact (@lem7235518 (term31 n f m)). Qed.
Lemma lem7235520 (m : nat) (f : nat -> real) (n : nat) : ((term32 m f n) = (term76 m f n)) = True.
Proof. exact (TRANS (@lem7235515 n f m) (@lem7235519 n f m)). Qed.
Lemma lem7235521 (m : nat) (f : nat -> real) (n : nat) : True = ((term32 m f n) = (term76 m f n)).
Proof. exact (SYM (@lem7235520 m f n)). Qed.
Lemma lem7235522 (m : nat) (f : nat -> real) (n : nat) : (term32 m f n) = (term76 m f n).
Proof. exact (EQ_MP (@lem7235521 m f n) (@lem0)). Qed.
Lemma lem7235534 : term60 = term36.
Proof. exact (EQ_MP (@lem1361604) (@lem1362040)). Qed.
Lemma lem7235535 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7235536 : term91 = term92.
Proof. exact (MK_COMB (@lem7235535) (@lem7235534)). Qed.
Lemma lem7235538 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7235539 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7235538 real t1 t2). Qed.
Lemma lem7235540 (m : nat) (f : nat -> real) (n : nat) : (term84 m f n) = term36.
Proof. exact (@lem7235539 (term32 m f n) term36). Qed.
Lemma lem7235541 (m : nat) (f : nat -> real) (n : nat) : (term60 = (term84 m f n)) = (term36 = term36).
Proof. exact (MK_COMB (@lem7235536) (@lem7235540 m f n)). Qed.
Lemma lem7235543 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7235544 (x : real) : (x = x) = True.
Proof. exact (@lem7235543 real x). Qed.
Lemma lem7235545 : (term36 = term36) = True.
Proof. exact (@lem7235544 term36). Qed.
Lemma lem7235546 (m : nat) (f : nat -> real) (n : nat) : (term60 = (term84 m f n)) = True.
Proof. exact (TRANS (@lem7235541 m f n) (@lem7235545)). Qed.
Lemma lem7235547 (m : nat) (f : nat -> real) (n : nat) : True = (term60 = (term84 m f n)).
Proof. exact (SYM (@lem7235546 m f n)). Qed.
Lemma lem7235548 (m : nat) (f : nat -> real) (n : nat) : term60 = (term84 m f n).
Proof. exact (EQ_MP (@lem7235547 m f n) (@lem0)). Qed.
Lemma lem7235549 (f : nat -> real) (m : nat) (n : nat) (h1 : term79 m n) : term60 = (term38 m f n).
Proof. exact (EQ_MP (@lem7235491 f m n h1) (@lem7235548 m f n)). Qed.
Lemma lem7235550 (f : nat -> real) (m : nat) (n : nat) (h1 : term79 m n) : (term79 m n) = (term60 = (term38 m f n)).
Proof. exact (prop_ext (fun h2 : term79 m n => @lem7235549 f m n h1) (fun h2 : term60 = (term38 m f n) => @lem7235476 m n h1)). Qed.
Lemma lem7235551 (f : nat -> real) (m : nat) (n : nat) (h1 : term79 m n) : term60 = (term38 m f n).
Proof. exact (EQ_MP (@lem7235550 f m n h1) (@lem7235476 m n h1)). Qed.
Lemma lem7235552 (m : nat) (f : nat -> real) (n : nat) : term63 m f n.
Proof. exact (fun h0 : term79 m n => @lem7235551 f m n h0). Qed.
Lemma lem7235553 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term32 m f n) = (term38 m f n).
Proof. exact (EQ_MP (@lem7235475 f m n h1) (@lem7235522 m f n)). Qed.
Lemma lem7235554 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = ((term32 m f n) = (term38 m f n)).
Proof. exact (prop_ext (fun h2 : Peano.le m n => @lem7235553 f m n h1) (fun h2 : (term32 m f n) = (term38 m f n) => @lem7235460 m n h1)). Qed.
Lemma lem7235555 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term32 m f n) = (term38 m f n).
Proof. exact (EQ_MP (@lem7235554 f m n h1) (@lem7235460 m n h1)). Qed.
Lemma lem7235556 (m : nat) (f : nat -> real) (n : nat) : term67 m f n.
Proof. exact (fun h0 : Peano.le m n => @lem7235555 f m n h0). Qed.
Lemma lem7235557 (m : nat) (f : nat -> real) (n : nat) : term70 m f n.
Proof. exact (conj (@lem7235556 m f n) (@lem7235552 m f n)). Qed.
Lemma lem7235558 (m : nat) (f : nat -> real) (n : nat) : (term49 m f n) = (term38 m f n).
Proof. exact (EQ_MP (@lem7235459 m f n) (@lem7235557 m f n)). Qed.
Lemma lem7235559 (m : nat) (f : nat -> real) (n : nat) : (term28 m n f) = (term38 m f n).
Proof. exact (EQ_MP (@lem7235441 m f n) (@lem7235558 m f n)). Qed.
Lemma lem7235560 (n : nat) (f : nat -> real) (m : nat) : (term27 m n f) = (term37 n f m).
Proof. exact (EQ_MP (@lem7235214 n f m) (@lem7235559 m f n)). Qed.
Lemma lem7235565 (f : nat -> real) (m : nat) : term93 f m.
Proof. exact (fun n : nat => @lem7235560 n f m). Qed.
Lemma lem7235570 (f : nat -> real) : term94 f.
Proof. exact (fun m : nat => @lem7235565 f m). Qed.
