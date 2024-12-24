Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_EQ_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EVEN_EXISTS_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EVEN_spec.
Require Import REAL_EQ_SQUARE_ABS_spec.
Require Import REAL_POW_EQ_ABS_spec.
Require Import REAL_POW_EQ_ODD_EQ_spec.
Require Import REAL_POW_POW_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm32_spec.
Require Import thm516372_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem1666515 (x : real) (m : nat) (n : nat) (h1 : (term0 x m n) = (term1 x m n)) : (term0 x m n) = (term1 x m n).
Proof. exact (h1). Qed.
Lemma lem1666516 (x : real) (m : nat) (n : nat) (h1 : (term0 x m n) = (term1 x m n)) : (term1 x m n) = (term0 x m n).
Proof. exact (SYM (@lem1666515 x m n h1)). Qed.
Lemma lem1666517 (x : real) (m : nat) (n : nat) (h1 : (term1 x m n) = (term0 x m n)) : (term1 x m n) = (term0 x m n).
Proof. exact (h1). Qed.
Lemma lem1666518 (x : real) (m : nat) (n : nat) (h1 : (term1 x m n) = (term0 x m n)) : (term0 x m n) = (term1 x m n).
Proof. exact (SYM (@lem1666517 x m n h1)). Qed.
Lemma lem1666519 (x : real) (m : nat) (n : nat) : ((term0 x m n) = (term1 x m n)) = ((term1 x m n) = (term0 x m n)).
Proof. exact (prop_ext (fun h1 : (term0 x m n) = (term1 x m n) => @lem1666516 x m n h1) (fun h1 : (term1 x m n) = (term0 x m n) => @lem1666518 x m n h1)). Qed.
Lemma lem1666520 (x : real) (m : nat) : (term2 x m) = (term3 x m).
Proof. exact (fun_ext (fun n : nat => @lem1666519 x m n)). Qed.
Lemma lem1666521 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1666522 (x : real) (m : nat) : (term4 x m) = (term5 x m).
Proof. exact (MK_COMB (@lem1666521) (@lem1666520 x m)). Qed.
Lemma lem1666523 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun m : nat => @lem1666522 x m)). Qed.
Lemma lem1666524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1666525 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1666524) (@lem1666523 x)). Qed.
Lemma lem1666526 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1666525 x)). Qed.
Lemma lem1666527 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666528 : term12 = term13.
Proof. exact (MK_COMB (@lem1666527) (@lem1666526)). Qed.
Lemma lem1666529 : term13.
Proof. exact (EQ_MP (@lem1666528) (@lem1640492)). Qed.
Lemma lem1666530 (n : nat) : term14 n.
Proof. exact (@lem128828 n). Qed.
Lemma lem1666531 (n : nat) : (term14 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term15 n)).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem1666533 (x : real) : term16 x.
Proof. exact (@lem1646031 x). Qed.
Lemma lem1666534 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1666535 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1666534 x) (@lem1666533 x)). Qed.
Lemma lem1666536 (x : real) (y : real) : term18 x y.
Proof. exact (@lem1666535 x y). Qed.
Lemma lem1666537 (x : real) (y : real) : (term18 x y) = (((real_abs x) = (real_abs y)) = ((term19 x) = (term19 y))).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1666539 (t1 : Prop) : term20 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1666540 (t1 : Prop) : (term20 t1) = (term21 t1).
Proof. exact (eq_refl (term20 t1)). Qed.
Lemma lem1666541 (t1 : Prop) : term21 t1.
Proof. exact (EQ_MP (@lem1666540 t1) (@lem1666539 t1)). Qed.
Lemma lem1666542 (t1 : Prop) (t2 : Prop) : term22 t1 t2.
Proof. exact (@lem1666541 t1 t2). Qed.
Lemma lem1666543 (t1 : Prop) (t2 : Prop) : (term22 t1 t2) = (term23 t1 t2).
Proof. exact (eq_refl (term22 t1 t2)). Qed.
Lemma lem1666544 (t1 : Prop) (t2 : Prop) : term23 t1 t2.
Proof. exact (EQ_MP (@lem1666543 t1 t2) (@lem1666542 t1 t2)). Qed.
Lemma lem1666545 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term24 t1 t2 t3.
Proof. exact (@lem1666544 t1 t2 t3). Qed.
Lemma lem1666546 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term24 t1 t2 t3) = ((term25 t1 t2 t3) = (term26 t1 t2 t3)).
Proof. exact (eq_refl (term24 t1 t2 t3)). Qed.
Lemma lem1666547 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term25 t1 t2 t3) = (term26 t1 t2 t3).
Proof. exact (EQ_MP (@lem1666546 t1 t2 t3) (@lem1666545 t1 t2 t3)). Qed.
Lemma lem1666548 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term26 t1 t2 t3) = (term25 t1 t2 t3).
Proof. exact (SYM (@lem1666547 t1 t2 t3)). Qed.
Lemma lem1666550 (n : nat) (h1 : (term27 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term27 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (h1). Qed.
Lemma lem1666551 (n : nat) (h1 : (term27 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term27 n).
Proof. exact (SYM (@lem1666550 n h1)). Qed.
Lemma lem1666552 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term27 n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term27 n).
Proof. exact (h1). Qed.
Lemma lem1666553 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term27 n)) : (term27 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem1666552 n h1)). Qed.
Lemma lem1666554 (n : nat) : ((term27 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term27 n)).
Proof. exact (prop_ext (fun h1 : (term27 n) = (Coq.Arith.PeanoNat.Nat.Odd n) => @lem1666551 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term27 n) => @lem1666553 n h1)). Qed.
Lemma lem1666555 : term28 = term29.
Proof. exact (fun_ext (fun n : nat => @lem1666554 n)). Qed.
Lemma lem1666556 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1666557 : term30 = term31.
Proof. exact (MK_COMB (@lem1666556) (@lem1666555)). Qed.
Lemma lem1666558 : term31.
Proof. exact (EQ_MP (@lem1666557) (@lem124715)). Qed.
Lemma lem1666559 (n : nat) : term32 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem1666560 (n : nat) : (term32 n) = (term33 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem1666561 (n : nat) : term33 n.
Proof. exact (EQ_MP (@lem1666560 n) (@lem1666559 n)). Qed.
Lemma lem1666563 (n : nat) (h1 : term34 n) : term34 n.
Proof. exact (h1). Qed.
Lemma lem1666897 : term35.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem1666898 : term36.
Proof. exact (proj2 (@lem1666897)). Qed.
Lemma lem1666951 : term37.
Proof. exact (proj1 (@lem1666897)). Qed.
Lemma lem1666952 (m : nat) : term38 m.
Proof. exact (@lem1666951 m). Qed.
Lemma lem1666953 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem1666954 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem1666953 m) (@lem1666952 m)). Qed.
Lemma lem1666955 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem1666954 m n). Qed.
Lemma lem1666956 (m : nat) (n : nat) : (term40 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem1666974 : term41.
Proof. exact (EQ_MP (@lem516372) (@lem0)). Qed.
Lemma lem1666975 : term42.
Proof. exact (proj2 (@lem1666974)). Qed.
Lemma lem1666986 : term43.
Proof. exact (proj1 (@lem1666974)). Qed.
Lemma lem1666987 (n : nat) : term44 n.
Proof. exact (@lem1666986 n). Qed.
Lemma lem1666988 (n : nat) : (term44 n) = ((term45 n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem1667218 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1667219 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1667220 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow x n) = (term46 x).
Proof. exact (MK_COMB (@lem1667219 x) (@lem1667218 n h1)). Qed.
Lemma lem1667222 (x : real) : (term46 x) = term47.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1667223 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow x n) = term47.
Proof. exact (TRANS (@lem1667220 x n h1) (@lem1667222 x)). Qed.
Lemma lem1667224 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1667225 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term48 x n) = term49.
Proof. exact (MK_COMB (@lem1667224) (@lem1667223 x n h1)). Qed.
Lemma lem1667227 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1667228 (y : real) : (real_pow y) = (real_pow y).
Proof. exact (eq_refl (real_pow y)). Qed.
Lemma lem1667229 (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow y n) = (term46 y).
Proof. exact (MK_COMB (@lem1667228 y) (@lem1667227 n h1)). Qed.
Lemma lem1667231 (x : real) : (term46 x) = term47.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1667232 (y : real) : (term46 y) = term47.
Proof. exact (@lem1667231 y). Qed.
Lemma lem1667233 (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow y n) = term47.
Proof. exact (TRANS (@lem1667229 y n h1) (@lem1667232 y)). Qed.
Lemma lem1667234 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : ((real_pow x n) = (real_pow y n)) = (term47 = term47).
Proof. exact (MK_COMB (@lem1667225 x n h1) (@lem1667233 y n h1)). Qed.
Lemma lem1667236 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1667237 (x : real) : (x = x) = True.
Proof. exact (@lem1667236 real x). Qed.
Lemma lem1667238 : (term47 = term47) = True.
Proof. exact (@lem1667237 term47). Qed.
Lemma lem1667239 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : ((real_pow x n) = (real_pow y n)) = True.
Proof. exact (TRANS (@lem1667234 x y n h1) (@lem1667238)). Qed.
Lemma lem1667240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1667241 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term50 x y n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1667240) (@lem1667239 x y n h1)). Qed.
Lemma lem1667243 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1667244 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem1667245 (n : nat) (h1 : n = (NUMERAL 0)) : (Coq.Arith.PeanoNat.Nat.Even n) = term51.
Proof. exact (MK_COMB (@lem1667244) (@lem1667243 n h1)). Qed.
Lemma lem1667247 (n : nat) : (term45 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1666988 n) (@lem1666987 n)). Qed.
Lemma lem1667248 : term51 = (Coq.Arith.PeanoNat.Nat.Even 0).
Proof. exact (@lem1667247 0). Qed.
Lemma lem1667250 : (Coq.Arith.PeanoNat.Nat.Even 0) = True.
Proof. exact (proj1 (@lem1666975)). Qed.
Lemma lem1667251 : term51 = True.
Proof. exact (TRANS (@lem1667248) (@lem1667250)). Qed.
Lemma lem1667252 (n : nat) (h1 : n = (NUMERAL 0)) : (Coq.Arith.PeanoNat.Nat.Even n) = True.
Proof. exact (TRANS (@lem1667245 n h1) (@lem1667251)). Qed.
Lemma lem1667253 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem1667254 (n : nat) (h1 : n = (NUMERAL 0)) : (term52 n) = (@COND Prop True).
Proof. exact (MK_COMB (@lem1667253) (@lem1667252 n h1)). Qed.
Lemma lem1667260 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1667261 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1667262 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term53.
Proof. exact (MK_COMB (@lem1667261) (@lem1667260 n h1)). Qed.
Lemma lem1667263 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1667264 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1667262 n h1) (@lem1667263)). Qed.
Lemma lem1667266 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1666956 m n) (@lem1666955 m n)). Qed.
Lemma lem1667267 : ((NUMERAL 0) = (NUMERAL 0)) = (0 = 0).
Proof. exact (@lem1667266 0 0). Qed.
Lemma lem1667269 : (0 = 0) = True.
Proof. exact (proj1 (@lem1666898)). Qed.
Lemma lem1667270 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1667267) (@lem1667269)). Qed.
Lemma lem1667271 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1667264 n h1) (@lem1667270)). Qed.
Lemma lem1667272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1667273 (n : nat) (h1 : n = (NUMERAL 0)) : (term54 n) = (or True).
Proof. exact (MK_COMB (@lem1667272) (@lem1667271 n h1)). Qed.
Lemma lem1667276 (x : real) (y : real) : ((real_abs x) = (real_abs y)) = ((real_abs x) = (real_abs y)).
Proof. exact (eq_refl ((real_abs x) = (real_abs y))). Qed.
Lemma lem1667277 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term55 n x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1667273 n h1) (@lem1667276 x y)). Qed.
Lemma lem1667279 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1667280 (x : real) (y : real) : (term56 x y) = True.
Proof. exact (@lem1667279 ((real_abs x) = (real_abs y))). Qed.
Lemma lem1667281 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term55 n x y) = True.
Proof. exact (TRANS (@lem1667277 x y n h1) (@lem1667280 x y)). Qed.
Lemma lem1667282 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term57 n x y) = (@COND Prop True True).
Proof. exact (MK_COMB (@lem1667254 n h1) (@lem1667281 x y n h1)). Qed.
Lemma lem1667285 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1667286 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term58 n x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1667282 x y n h1) (@lem1667285 x y)). Qed.
Lemma lem1667288 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1667289 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem1667288 Prop t2 t1). Qed.
Lemma lem1667290 (x : real) (y : real) : (term59 x y) = True.
Proof. exact (@lem1667289 (x = y) True). Qed.
Lemma lem1667291 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term58 n x y) = True.
Proof. exact (TRANS (@lem1667286 x y n h1) (@lem1667290 x y)). Qed.
Lemma lem1667292 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (((real_pow x n) = (real_pow y n)) = (term58 n x y)) = (True = True).
Proof. exact (MK_COMB (@lem1667241 x y n h1) (@lem1667291 x y n h1)). Qed.
Lemma lem1667294 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1667295 : (True = True) = True.
Proof. exact (@lem1667294 True). Qed.
Lemma lem1667296 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (((real_pow x n) = (real_pow y n)) = (term58 n x y)) = True.
Proof. exact (TRANS (@lem1667292 x y n h1) (@lem1667295)). Qed.
Lemma lem1667297 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : True = (((real_pow x n) = (real_pow y n)) = (term58 n x y)).
Proof. exact (SYM (@lem1667296 x y n h1)). Qed.
Lemma lem1667298 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : ((real_pow x n) = (real_pow y n)) = (term58 n x y).
Proof. exact (EQ_MP (@lem1667297 x y n h1) (@lem0)). Qed.
Lemma lem1667948 (n : nat) : term60 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1667968 (n : nat) (h1 : term34 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1667948 n (@lem1666563 n h1)). Qed.
Lemma lem1667969 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1667970 (n : nat) (h1 : term34 n) : (term54 n) = (or False).
Proof. exact (MK_COMB (@lem1667969) (@lem1667968 n h1)). Qed.
Lemma lem1667973 (x : real) (y : real) : ((real_abs x) = (real_abs y)) = ((real_abs x) = (real_abs y)).
Proof. exact (eq_refl ((real_abs x) = (real_abs y))). Qed.
Lemma lem1667974 (x : real) (y : real) (n : nat) (h1 : term34 n) : (term55 n x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1667970 n h1) (@lem1667973 x y)). Qed.
Lemma lem1667976 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1667977 (x : real) (y : real) : (term61 x y) = ((real_abs x) = (real_abs y)).
Proof. exact (@lem1667976 ((real_abs x) = (real_abs y))). Qed.
Lemma lem1667980 (x : real) (y : real) (n : nat) (h1 : term34 n) : (term55 n x y) = ((real_abs x) = (real_abs y)).
Proof. exact (TRANS (@lem1667974 x y n h1) (@lem1667977 x y)). Qed.
Lemma lem1667981 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1667982 (x : real) (y : real) (n : nat) (h1 : term34 n) : (term57 n x y) = (term62 n x y).
Proof. exact (MK_COMB (@lem1667981 n) (@lem1667980 x y n h1)). Qed.
Lemma lem1667985 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1667986 (x : real) (y : real) (n : nat) (h1 : term34 n) : (term58 n x y) = (term63 n x y).
Proof. exact (MK_COMB (@lem1667982 x y n h1) (@lem1667985 x y)). Qed.
Lemma lem1667987 (x : real) (y : real) (n : nat) : (term50 x y n) = (term50 x y n).
Proof. exact (eq_refl (term50 x y n)). Qed.
Lemma lem1667988 (x : real) (y : real) (n : nat) (h1 : term34 n) : (((real_pow x n) = (real_pow y n)) = (term58 n x y)) = (((real_pow x n) = (real_pow y n)) = (term63 n x y)).
Proof. exact (MK_COMB (@lem1667987 x y n) (@lem1667986 x y n h1)). Qed.
Lemma lem1667991 (x : real) (y : real) (n : nat) (h1 : term34 n) : (((real_pow x n) = (real_pow y n)) = (term63 n x y)) = (((real_pow x n) = (real_pow y n)) = (term58 n x y)).
Proof. exact (SYM (@lem1667988 x y n h1)). Qed.
Lemma lem1667992 (_474 : Prop) (_475 : Prop) (_476 : Prop -> Prop) (_477 : Prop) : (term64 _476 _475 _474 _477) = (term65 _474 _475 _476 _477).
Proof. exact (@lem13473 Prop _474 _475 _476 _477). Qed.
Lemma lem1667993 (_474 : Prop) (_475 : Prop) (x : real) (y : real) (n : nat) (_477 : Prop) : (term66 x y n _475 _474 _477) = (term67 _474 _475 x y n _477).
Proof. exact (@lem1667992 _474 _475 (term68 x y n) _477). Qed.
Lemma lem1667994 (n : nat) (x : real) (y : real) : (term69 n x y) = (term70 n x y).
Proof. exact (@lem1667993 ((real_abs x) = (real_abs y)) (Coq.Arith.PeanoNat.Nat.Even n) x y n (x = y)). Qed.
Lemma lem1667995 (n : nat) (x : real) (y : real) : (term71 n x y) = (((real_pow x n) = (real_pow y n)) = (x = y)).
Proof. exact (eq_refl (term71 n x y)). Qed.
Lemma lem1667996 (n : nat) : (term72 n) = (term72 n).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem1667997 (n : nat) (x : real) (y : real) : (term73 n x y) = (term74 n x y).
Proof. exact (MK_COMB (@lem1667996 n) (@lem1667995 n x y)). Qed.
Lemma lem1667998 (n : nat) (x : real) (y : real) : (term75 n x y) = (((real_pow x n) = (real_pow y n)) = ((real_abs x) = (real_abs y))).
Proof. exact (eq_refl (term75 n x y)). Qed.
Lemma lem1667999 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem1668000 (n : nat) (x : real) (y : real) : (term77 n x y) = (term78 n x y).
Proof. exact (MK_COMB (@lem1667999 n) (@lem1667998 n x y)). Qed.
Lemma lem1668001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1668002 (n : nat) (x : real) (y : real) : (term79 n x y) = (term80 n x y).
Proof. exact (MK_COMB (@lem1668001) (@lem1668000 n x y)). Qed.
Lemma lem1668003 (n : nat) (x : real) (y : real) : (term70 n x y) = (term81 n x y).
Proof. exact (MK_COMB (@lem1668002 n x y) (@lem1667997 n x y)). Qed.
Lemma lem1668004 (n : nat) (x : real) (y : real) : (term69 n x y) = (((real_pow x n) = (real_pow y n)) = (term63 n x y)).
Proof. exact (eq_refl (term69 n x y)). Qed.
Lemma lem1668005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1668006 (n : nat) (x : real) (y : real) : (term82 n x y) = (term83 n x y).
Proof. exact (MK_COMB (@lem1668005) (@lem1668004 n x y)). Qed.
Lemma lem1668007 (n : nat) (x : real) (y : real) : ((term69 n x y) = (term70 n x y)) = ((((real_pow x n) = (real_pow y n)) = (term63 n x y)) = (term81 n x y)).
Proof. exact (MK_COMB (@lem1668006 n x y) (@lem1668003 n x y)). Qed.
Lemma lem1668008 (n : nat) (x : real) (y : real) : (((real_pow x n) = (real_pow y n)) = (term63 n x y)) = (term81 n x y).
Proof. exact (EQ_MP (@lem1668007 n x y) (@lem1667994 n x y)). Qed.
Lemma lem1668009 (n : nat) (x : real) (y : real) : (term81 n x y) = (((real_pow x n) = (real_pow y n)) = (term63 n x y)).
Proof. exact (SYM (@lem1668008 n x y)). Qed.
Lemma lem1668010 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem1668027 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (h1). Qed.
Lemma lem1668099 (n : nat) : term84 n.
Proof. exact (@lem1666558 n). Qed.
Lemma lem1668100 (n : nat) : (term84 n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term27 n)).
Proof. exact (eq_refl (term84 n)). Qed.
Lemma lem1668102 (n : nat) : term85 n.
Proof. exact (@lem1665320 n). Qed.
Lemma lem1668103 (n : nat) : (term85 n) = (term86 n).
Proof. exact (eq_refl (term85 n)). Qed.
Lemma lem1668104 (n : nat) : term86 n.
Proof. exact (EQ_MP (@lem1668103 n) (@lem1668102 n)). Qed.
Lemma lem1668105 (n : nat) (x : real) : term87 n x.
Proof. exact (@lem1668104 n x). Qed.
Lemma lem1668106 (n : nat) (x : real) : (term87 n x) = (term88 n x).
Proof. exact (eq_refl (term87 n x)). Qed.
Lemma lem1668107 (n : nat) (x : real) : term88 n x.
Proof. exact (EQ_MP (@lem1668106 n x) (@lem1668105 n x)). Qed.
Lemma lem1668108 (n : nat) (x : real) (y : real) : term89 n x y.
Proof. exact (@lem1668107 n x y). Qed.
Lemma lem1668109 (n : nat) (x : real) (y : real) : (term89 n x y) = (term90 n x y).
Proof. exact (eq_refl (term89 n x y)). Qed.
Lemma lem1668110 (n : nat) (x : real) (y : real) : term90 n x y.
Proof. exact (EQ_MP (@lem1668109 n x y) (@lem1668108 n x y)). Qed.
Lemma lem1668111 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem1668112 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : ((real_pow x n) = (real_pow y n)) = (x = y).
Proof. exact (@lem1668110 n x y (@lem1668111 n h1)). Qed.
Lemma lem1668131 (n : nat) : term91 n.
Proof. exact (@lem82 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1668136 (n : nat) (x : real) (y : real) : term90 n x y.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Odd n => @lem1668112 x y n h0). Qed.
Lemma lem1668138 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term27 n).
Proof. exact (EQ_MP (@lem1668100 n) (@lem1668099 n)). Qed.
Lemma lem1668140 (n : nat) (h1 : term27 n) : (Coq.Arith.PeanoNat.Nat.Even n) = False.
Proof. exact (@lem1668131 n (@lem1668027 n h1)). Qed.
Lemma lem1668141 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1668142 (n : nat) (h1 : term27 n) : (term27 n) = (~ False).
Proof. exact (MK_COMB (@lem1668141) (@lem1668140 n h1)). Qed.
Lemma lem1668144 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1668145 (n : nat) (h1 : term27 n) : (term27 n) = True.
Proof. exact (TRANS (@lem1668142 n h1) (@lem1668144)). Qed.
Lemma lem1668146 (n : nat) (h1 : term27 n) : (Coq.Arith.PeanoNat.Nat.Odd n) = True.
Proof. exact (TRANS (@lem1668138 n) (@lem1668145 n h1)). Qed.
Lemma lem1668147 (n : nat) (h1 : term27 n) : True = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem1668146 n h1)). Qed.
Lemma lem1668148 (n : nat) (h1 : term27 n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (EQ_MP (@lem1668147 n h1) (@lem0)). Qed.
Lemma lem1668149 (x : real) (y : real) (n : nat) (h1 : term27 n) : ((real_pow x n) = (real_pow y n)) = (x = y).
Proof. exact (@lem1668136 n x y (@lem1668148 n h1)). Qed.
Lemma lem1668152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1668153 (x : real) (y : real) (n : nat) (h1 : term27 n) : (term50 x y n) = (term92 x y).
Proof. exact (MK_COMB (@lem1668152) (@lem1668149 x y n h1)). Qed.
Lemma lem1668158 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1668159 (x : real) (y : real) (n : nat) (h1 : term27 n) : (((real_pow x n) = (real_pow y n)) = (x = y)) = ((x = y) = (x = y)).
Proof. exact (MK_COMB (@lem1668153 x y n h1) (@lem1668158 x y)). Qed.
Lemma lem1668161 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1668162 (x : Prop) : (x = x) = True.
Proof. exact (@lem1668161 Prop x). Qed.
Lemma lem1668163 (x : real) (y : real) : ((x = y) = (x = y)) = True.
Proof. exact (@lem1668162 (x = y)). Qed.
Lemma lem1668164 (x : real) (y : real) (n : nat) (h1 : term27 n) : (((real_pow x n) = (real_pow y n)) = (x = y)) = True.
Proof. exact (TRANS (@lem1668159 x y n h1) (@lem1668163 x y)). Qed.
Lemma lem1668165 (x : real) (y : real) (n : nat) (h1 : term27 n) : True = (((real_pow x n) = (real_pow y n)) = (x = y)).
Proof. exact (SYM (@lem1668164 x y n h1)). Qed.
Lemma lem1668168 (p : Prop) : p = (term93 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1668169 (n : nat) (x : real) (y : real) : (term94 n x y) = (term95 n x y).
Proof. exact (@lem1668168 (term94 n x y)). Qed.
Lemma lem1668170 (n : nat) (x : real) (y : real) : (term95 n x y) = (term94 n x y).
Proof. exact (SYM (@lem1668169 n x y)). Qed.
Lemma lem1668171 (n : nat) (x : real) (y : real) (h1 : term96 n x y) : term96 n x y.
Proof. exact (h1). Qed.
Lemma lem1668174 (n : nat) (x : real) (y : real) (h1 : term97 n x y) : term97 n x y.
Proof. exact (h1). Qed.
Lemma lem1668175 (n : nat) (x : real) (y : real) : term98 n x y.
Proof. exact (fun h0 : term97 n x y => @lem1668174 n x y h0). Qed.
Lemma lem1668176 (n : nat) (x : real) (y : real) (h1 : term98 n x y) : term98 n x y.
Proof. exact (h1). Qed.
Lemma lem1668177 (n : nat) (x : real) (y : real) (h1 : term97 n x y) : term97 n x y.
Proof. exact (h1). Qed.
Lemma lem1668178 (n : nat) (x : real) (y : real) (h1 : term97 n x y) (h2 : term98 n x y) : term97 n x y.
Proof. exact (@lem1668176 n x y h2 (@lem1668177 n x y h1)). Qed.
Lemma lem1668179 (n : nat) (x : real) (y : real) (h1 : term97 n x y) : term99 n x y.
Proof. exact (fun h0 : term98 n x y => @lem1668178 n x y h1 h0). Qed.
Lemma lem1668180 (n : nat) (x : real) (y : real) (h1 : term98 n x y) : term98 n x y.
Proof. exact (h1). Qed.
Lemma lem1668181 (n : nat) (x : real) (y : real) (h1 : term97 n x y) (h2 : term98 n x y) : term97 n x y.
Proof. exact (@lem1668179 n x y h1 (@lem1668180 n x y h2)). Qed.
Lemma lem1668182 (n : nat) (x : real) (y : real) (h1 : term98 n x y) : term98 n x y.
Proof. exact (fun h0 : term97 n x y => @lem1668181 n x y h0 h1). Qed.
Lemma lem1668183 (n : nat) (x : real) (y : real) : term100 n x y.
Proof. exact (fun h0 : term98 n x y => @lem1668182 n x y h0). Qed.
Lemma lem1668186 (n : nat) (x : real) (y : real) : term98 n x y.
Proof. exact (@lem1668183 n x y (@lem1668175 n x y)). Qed.
Lemma lem1668208 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1668209 : term101 = term102.
Proof. exact (@lem1668208 term103). Qed.
Lemma lem1668226 (n : nat) (x : real) (y : real) : (term104 n x y) = (term104 n x y).
Proof. exact (eq_refl (term104 n x y)). Qed.
Lemma lem1668227 (n : nat) (x : real) (y : real) : (term105 n x y) = (term106 n x y).
Proof. exact (MK_COMB (@lem1668226 n x y) (@lem1668209)). Qed.
Lemma lem1668230 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem1668231 (n : nat) (x : real) (y : real) : (term107 n x y) = (term108 n x y).
Proof. exact (MK_COMB (@lem1668230 n) (@lem1668227 n x y)). Qed.
Lemma lem1668234 (n : nat) : (term109 n) = (term109 n).
Proof. exact (eq_refl (term109 n)). Qed.
Lemma lem1668235 (n : nat) (x : real) (y : real) : (term97 n x y) = (term110 n x y).
Proof. exact (MK_COMB (@lem1668234 n) (@lem1668231 n x y)). Qed.
Lemma lem1668238 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (fun_ext (fun n : nat => @lem1668235 n x y)). Qed.
Lemma lem1668239 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1668240 (x : real) (y : real) : (term113 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1668239) (@lem1668238 x y)). Qed.
Lemma lem1668245 (y : real) : (term115 y) = (term116 y).
Proof. exact (fun_ext (fun x : real => @lem1668240 x y)). Qed.
Lemma lem1668246 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668247 (y : real) : (term117 y) = (term118 y).
Proof. exact (MK_COMB (@lem1668246) (@lem1668245 y)). Qed.
Lemma lem1668252 : term119 = term120.
Proof. exact (fun_ext (fun y : real => @lem1668247 y)). Qed.
Lemma lem1668253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668262 : term121 = term122.
Proof. exact (MK_COMB (@lem1668253) (@lem1668252)). Qed.
Lemma lem1668273 (n : nat) (x : real) (y : real) : (term123 n x y) = (term123 n x y).
Proof. exact (eq_refl (term123 n x y)). Qed.
Lemma lem1668274 (n : nat) (x : real) : (term124 n x) = (term124 n x).
Proof. exact (fun_ext (fun y : real => @lem1668273 n x y)). Qed.
Lemma lem1668275 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668276 (n : nat) (x : real) : (term125 n x) = (term125 n x).
Proof. exact (MK_COMB (@lem1668275) (@lem1668274 n x)). Qed.
Lemma lem1668277 (n : nat) : (term126 n) = (term126 n).
Proof. exact (fun_ext (fun x : real => @lem1668276 n x)). Qed.
Lemma lem1668278 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668279 (n : nat) : (term127 n) = (term127 n).
Proof. exact (MK_COMB (@lem1668278) (@lem1668277 n)). Qed.
Lemma lem1668280 : term128 = term128.
Proof. exact (fun_ext (fun n : nat => @lem1668279 n)). Qed.
Lemma lem1668281 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1668282 : term103 = term103.
Proof. exact (MK_COMB (@lem1668281) (@lem1668280)). Qed.
Lemma lem1668283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1668284 : term102 = term102.
Proof. exact (MK_COMB (@lem1668283) (@lem1668282)). Qed.
Lemma lem1668293 (n : nat) (x : real) (y : real) : (term104 n x y) = (term104 n x y).
Proof. exact (eq_refl (term104 n x y)). Qed.
Lemma lem1668294 (n : nat) (x : real) (y : real) : (term106 n x y) = (term106 n x y).
Proof. exact (MK_COMB (@lem1668293 n x y) (@lem1668284)). Qed.
Lemma lem1668297 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem1668298 (n : nat) (x : real) (y : real) : (term108 n x y) = (term108 n x y).
Proof. exact (MK_COMB (@lem1668297 n) (@lem1668294 n x y)). Qed.
Lemma lem1668303 (n : nat) : (term109 n) = (term109 n).
Proof. exact (eq_refl (term109 n)). Qed.
Lemma lem1668304 (n : nat) (x : real) (y : real) : (term110 n x y) = (term110 n x y).
Proof. exact (MK_COMB (@lem1668303 n) (@lem1668298 n x y)). Qed.
Lemma lem1668305 (x : real) (y : real) : (term112 x y) = (term112 x y).
Proof. exact (fun_ext (fun n : nat => @lem1668304 n x y)). Qed.
Lemma lem1668306 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1668307 (x : real) (y : real) : (term114 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1668306) (@lem1668305 x y)). Qed.
Lemma lem1668308 (y : real) : (term116 y) = (term116 y).
Proof. exact (fun_ext (fun x : real => @lem1668307 x y)). Qed.
Lemma lem1668309 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668310 (y : real) : (term118 y) = (term118 y).
Proof. exact (MK_COMB (@lem1668309) (@lem1668308 y)). Qed.
Lemma lem1668311 : term120 = term120.
Proof. exact (fun_ext (fun y : real => @lem1668310 y)). Qed.
Lemma lem1668312 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668313 : term122 = term122.
Proof. exact (MK_COMB (@lem1668312) (@lem1668311)). Qed.
Lemma lem1668364 : term121 = term122.
Proof. exact (TRANS (@lem1668262) (@lem1668313)). Qed.
Lemma lem1668365 : term122 = term121.
Proof. exact (SYM (@lem1668364)). Qed.
Lemma lem1668368 (n : nat) (x : real) (y : real) (h1 : term96 n x y) : term96 n x y.
Proof. exact (h1). Qed.
Lemma lem1668369 (h1 : term103) : term103.
Proof. exact (h1). Qed.
Lemma lem1668375 (n : nat) (h1 : term34 n) : term34 n.
Proof. exact (h1). Qed.
Lemma lem1668392 (n : nat) (x : real) (y : real) : (term96 n x y) = (term129 n x y).
Proof. exact (@lem17362 ((real_pow x n) = (real_pow y n)) ((real_abs x) = (real_abs y))). Qed.
Lemma lem1668396 (n : nat) : (term130 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem1668397 (x : real) (y : real) (n : nat) : (term131 x y n) = (term131 x y n).
Proof. exact (eq_refl (term131 x y n)). Qed.
Lemma lem1668398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1668399 (n : nat) : (term132 n) = (term54 n).
Proof. exact (MK_COMB (@lem1668398) (@lem1668396 n)). Qed.
Lemma lem1668400 (x : real) (y : real) (n : nat) : (term133 x y n) = (term134 x y n).
Proof. exact (MK_COMB (@lem1668399 n) (@lem1668397 x y n)). Qed.
Lemma lem1668401 (x : real) (y : real) (n : nat) : (term135 x y n) = (term133 x y n).
Proof. exact (@lem17045 (term34 n) ((real_pow x n) = (real_pow y n))). Qed.
Lemma lem1668402 (x : real) (y : real) (n : nat) : (term135 x y n) = (term134 x y n).
Proof. exact (TRANS (@lem1668401 x y n) (@lem1668400 x y n)). Qed.
Lemma lem1668403 (x : real) (y : real) : ((real_abs x) = (real_abs y)) = ((real_abs x) = (real_abs y)).
Proof. exact (eq_refl ((real_abs x) = (real_abs y))). Qed.
Lemma lem1668404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1668405 (x : real) (y : real) (n : nat) : (term136 x y n) = (term137 x y n).
Proof. exact (MK_COMB (@lem1668404) (@lem1668402 x y n)). Qed.
Lemma lem1668406 (n : nat) (x : real) (y : real) : (term138 n x y) = (term139 n x y).
Proof. exact (MK_COMB (@lem1668405 x y n) (@lem1668403 x y)). Qed.
Lemma lem1668407 (n : nat) (x : real) (y : real) : (term123 n x y) = (term138 n x y).
Proof. exact (@lem17265 (term140 x y n) ((real_abs x) = (real_abs y))). Qed.
Lemma lem1668408 (n : nat) (x : real) (y : real) : (term123 n x y) = (term139 n x y).
Proof. exact (TRANS (@lem1668407 n x y) (@lem1668406 n x y)). Qed.
Lemma lem1668409 (n : nat) (x : real) : (term124 n x) = (term141 n x).
Proof. exact (fun_ext (fun y : real => @lem1668408 n x y)). Qed.
Lemma lem1668410 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668411 (n : nat) (x : real) : (term125 n x) = (term142 n x).
Proof. exact (MK_COMB (@lem1668410) (@lem1668409 n x)). Qed.
Lemma lem1668412 (n : nat) : (term126 n) = (term143 n).
Proof. exact (fun_ext (fun x : real => @lem1668411 n x)). Qed.
Lemma lem1668413 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668414 (n : nat) : (term127 n) = (term144 n).
Proof. exact (MK_COMB (@lem1668413) (@lem1668412 n)). Qed.
Lemma lem1668415 : term128 = term145.
Proof. exact (fun_ext (fun n : nat => @lem1668414 n)). Qed.
Lemma lem1668416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1668477 : term103 = term146.
Proof. exact (MK_COMB (@lem1668416) (@lem1668415)). Qed.
Lemma lem1668478 (h1 : term103) : term146.
Proof. exact (EQ_MP (@lem1668477) (@lem1668369 h1)). Qed.
Lemma lem1668488 (n : nat) (h1 : term34 n) : term34 n.
Proof. exact (h1). Qed.
Lemma lem1668520 (n : nat) (x : real) (y : real) (h1 : term96 n x y) : term129 n x y.
Proof. exact (EQ_MP (@lem1668392 n x y) (@lem1668368 n x y h1)). Qed.
Lemma lem1668557 (n : nat) (x : real) (y : real) : (term139 n x y) = (term139 n x y).
Proof. exact (eq_refl (term139 n x y)). Qed.
Lemma lem1668558 (n : nat) (x : real) : (term141 n x) = (term141 n x).
Proof. exact (fun_ext (fun y : real => @lem1668557 n x y)). Qed.
Lemma lem1668559 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668560 (n : nat) (x : real) : (term142 n x) = (term142 n x).
Proof. exact (MK_COMB (@lem1668559) (@lem1668558 n x)). Qed.
Lemma lem1668561 (n : nat) : (term143 n) = (term143 n).
Proof. exact (fun_ext (fun x : real => @lem1668560 n x)). Qed.
Lemma lem1668562 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668563 (n : nat) : (term144 n) = (term144 n).
Proof. exact (MK_COMB (@lem1668562) (@lem1668561 n)). Qed.
Lemma lem1668564 : term145 = term145.
Proof. exact (fun_ext (fun n : nat => @lem1668563 n)). Qed.
Lemma lem1668565 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1668566 : term146 = term146.
Proof. exact (MK_COMB (@lem1668565) (@lem1668564)). Qed.
Lemma lem1668567 (h1 : term103) : term146.
Proof. exact (EQ_MP (@lem1668566) (@lem1668478 h1)). Qed.
Lemma lem1668573 (n : nat) (h1 : term34 n) : term34 n.
Proof. exact (h1). Qed.
Lemma lem1668591 (n : nat) (x : real) (y : real) : (term139 n x y) = (term139 n x y).
Proof. exact (eq_refl (term139 n x y)). Qed.
Lemma lem1668592 (n : nat) (x : real) : (term141 n x) = (term141 n x).
Proof. exact (fun_ext (fun y : real => @lem1668591 n x y)). Qed.
Lemma lem1668593 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668594 (n : nat) (x : real) : (term142 n x) = (term142 n x).
Proof. exact (MK_COMB (@lem1668593) (@lem1668592 n x)). Qed.
Lemma lem1668595 (n : nat) : (term143 n) = (term143 n).
Proof. exact (fun_ext (fun x : real => @lem1668594 n x)). Qed.
Lemma lem1668596 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1668597 (n : nat) : (term144 n) = (term144 n).
Proof. exact (MK_COMB (@lem1668596) (@lem1668595 n)). Qed.
Lemma lem1668598 : term145 = term145.
Proof. exact (fun_ext (fun n : nat => @lem1668597 n)). Qed.
Lemma lem1668599 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1668601 : term146 = term146.
Proof. exact (MK_COMB (@lem1668599) (@lem1668598)). Qed.
Lemma lem1668602 (h1 : term103) : term146.
Proof. exact (EQ_MP (@lem1668601) (@lem1668567 h1)). Qed.
Lemma lem1668611 (_25780 : nat) (h1 : term103) : term147 _25780.
Proof. exact (@lem1668602 h1 _25780). Qed.
Lemma lem1668612 (_25780 : nat) : (term147 _25780) = (term144 _25780).
Proof. exact (eq_refl (term147 _25780)). Qed.
Lemma lem1668613 (_25780 : nat) (h1 : term103) : term144 _25780.
Proof. exact (EQ_MP (@lem1668612 _25780) (@lem1668611 _25780 h1)). Qed.
Lemma lem1668614 (_25780 : nat) (_25781 : real) (h1 : term103) : term148 _25780 _25781.
Proof. exact (@lem1668613 _25780 h1 _25781). Qed.
Lemma lem1668615 (_25780 : nat) (_25781 : real) : (term148 _25780 _25781) = (term142 _25780 _25781).
Proof. exact (eq_refl (term148 _25780 _25781)). Qed.
Lemma lem1668616 (_25780 : nat) (_25781 : real) (h1 : term103) : term142 _25780 _25781.
Proof. exact (EQ_MP (@lem1668615 _25780 _25781) (@lem1668614 _25780 _25781 h1)). Qed.
Lemma lem1668617 (_25780 : nat) (_25781 : real) (_25782 : real) (h1 : term103) : term149 _25780 _25781 _25782.
Proof. exact (@lem1668616 _25780 _25781 h1 _25782). Qed.
Lemma lem1668618 (_25780 : nat) (_25781 : real) (_25782 : real) : (term149 _25780 _25781 _25782) = (term139 _25780 _25781 _25782).
Proof. exact (eq_refl (term149 _25780 _25781 _25782)). Qed.
Lemma lem1668619 (_25780 : nat) (_25781 : real) (_25782 : real) (h1 : term103) : term139 _25780 _25781 _25782.
Proof. exact (EQ_MP (@lem1668618 _25780 _25781 _25782) (@lem1668617 _25780 _25781 _25782 h1)). Qed.
Lemma lem1668621 (n : nat) (h1 : term34 n) : term34 n.
Proof. exact (h1). Qed.
Lemma lem1668634 (_25780 : nat) (_25781 : real) (_25782 : real) : (term139 _25780 _25781 _25782) = (term150 _25780 _25781 _25782).
Proof. exact (@lem1666548 (_25780 = (NUMERAL 0)) (term131 _25781 _25782 _25780) ((real_abs _25781) = (real_abs _25782))). Qed.
Lemma lem1668635 (_25780 : nat) (_25781 : real) (_25782 : real) (h1 : term103) : term150 _25780 _25781 _25782.
Proof. exact (EQ_MP (@lem1668634 _25780 _25781 _25782) (@lem1668619 _25780 _25781 _25782 h1)). Qed.
Lemma lem1668639 (n : nat) (x : real) (y : real) (h1 : term96 n x y) : term151 x y.
Proof. exact (proj2 (@lem1668520 n x y h1)). Qed.
Lemma lem1668688 (n : nat) (h1 : term34 n) : term34 n.
Proof. exact (h1). Qed.
Lemma lem1668689 (n : nat) (h1 : term34 n) : term152 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem1668688 n h1). Qed.
Lemma lem1668691 (p : Prop) : (term153 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1668692 (n : nat) : (term152 n) = (term34 n).
Proof. exact (@lem1668691 (n = (NUMERAL 0))). Qed.
Lemma lem1668693 (n : nat) (h1 : term34 n) : term34 n.
Proof. exact (EQ_MP (@lem1668692 n) (@lem1668689 n h1)). Qed.
Lemma lem1668695 (n : nat) (x : real) (y : real) (h1 : term96 n x y) : (real_pow x n) = (real_pow y n).
Proof. exact (proj1 (@lem1668520 n x y h1)). Qed.
Lemma lem1668696 (n : nat) (x : real) (y : real) (h1 : term96 n x y) : term154 x y n.
Proof. exact (fun h0 : term131 x y n => @lem1668695 n x y h1). Qed.
Lemma lem1668698 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1668699 (x : real) (y : real) (n : nat) : (term154 x y n) = ((real_pow x n) = (real_pow y n)).
Proof. exact (@lem1668698 ((real_pow x n) = (real_pow y n))). Qed.
Lemma lem1668700 (n : nat) (x : real) (y : real) (h1 : term96 n x y) : (real_pow x n) = (real_pow y n).
Proof. exact (EQ_MP (@lem1668699 x y n) (@lem1668696 n x y h1)). Qed.
Lemma lem1668718 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1668719 (_25781 : real) (_25782 : real) (_25780 : nat) : (term156 _25780 _25781 _25782) = (term157 _25781 _25782 _25780).
Proof. exact (@lem1668718 ((real_abs _25781) = (real_abs _25782)) (term131 _25781 _25782 _25780)). Qed.
Lemma lem1668729 (_25780 : nat) : (term54 _25780) = (term54 _25780).
Proof. exact (eq_refl (term54 _25780)). Qed.
Lemma lem1668730 (_25781 : real) (_25782 : real) (_25780 : nat) : (term150 _25780 _25781 _25782) = (term158 _25781 _25782 _25780).
Proof. exact (MK_COMB (@lem1668729 _25780) (@lem1668719 _25781 _25782 _25780)). Qed.
Lemma lem1668741 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1668742 (_25781 : real) (_25782 : real) (_25780 : nat) : (term159 _25780 _25781 _25782) = (term160 _25781 _25782 _25780).
Proof. exact (MK_COMB (@lem1668741) (@lem1668730 _25781 _25782 _25780)). Qed.
Lemma lem1668746 (q : Prop) (p : Prop) (r : Prop) : (term25 p q r) = (term25 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1668747 (_25781 : real) (_25782 : real) (_25780 : nat) : (term161 _25781 _25782 _25780) = (term158 _25781 _25782 _25780).
Proof. exact (@lem1668746 (_25780 = (NUMERAL 0)) ((real_abs _25781) = (real_abs _25782)) (term131 _25781 _25782 _25780)). Qed.
Lemma lem1668769 (_25781 : real) (_25782 : real) (_25780 : nat) : ((term150 _25780 _25781 _25782) = (term161 _25781 _25782 _25780)) = ((term158 _25781 _25782 _25780) = (term158 _25781 _25782 _25780)).
Proof. exact (MK_COMB (@lem1668742 _25781 _25782 _25780) (@lem1668747 _25781 _25782 _25780)). Qed.
Lemma lem1668771 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1668772 (x : Prop) : (x = x) = True.
Proof. exact (@lem1668771 Prop x). Qed.
Lemma lem1668773 (_25781 : real) (_25782 : real) (_25780 : nat) : ((term158 _25781 _25782 _25780) = (term158 _25781 _25782 _25780)) = True.
Proof. exact (@lem1668772 (term158 _25781 _25782 _25780)). Qed.
Lemma lem1668774 (_25781 : real) (_25782 : real) (_25780 : nat) : ((term150 _25780 _25781 _25782) = (term161 _25781 _25782 _25780)) = True.
Proof. exact (TRANS (@lem1668769 _25781 _25782 _25780) (@lem1668773 _25781 _25782 _25780)). Qed.
Lemma lem1668775 (_25781 : real) (_25782 : real) (_25780 : nat) : True = ((term150 _25780 _25781 _25782) = (term161 _25781 _25782 _25780)).
Proof. exact (SYM (@lem1668774 _25781 _25782 _25780)). Qed.
Lemma lem1668776 (_25781 : real) (_25782 : real) (_25780 : nat) : (term150 _25780 _25781 _25782) = (term161 _25781 _25782 _25780).
Proof. exact (EQ_MP (@lem1668775 _25781 _25782 _25780) (@lem0)). Qed.
Lemma lem1668777 (_25781 : real) (_25782 : real) (_25780 : nat) (h1 : term103) : term161 _25781 _25782 _25780.
Proof. exact (EQ_MP (@lem1668776 _25781 _25782 _25780) (@lem1668635 _25780 _25781 _25782 h1)). Qed.
Lemma lem1668779 (b : Prop) (a : Prop) : (a \/ b) = (term162 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1668780 (_25780 : nat) (_25781 : real) (_25782 : real) : (term161 _25781 _25782 _25780) = (term163 _25780 _25781 _25782).
Proof. exact (@lem1668779 (term134 _25781 _25782 _25780) ((real_abs _25781) = (real_abs _25782))). Qed.
Lemma lem1668782 (a : Prop) (b : Prop) : (term164 a b) = (term165 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1668783 (_25781 : real) (_25782 : real) (_25780 : nat) : (term166 _25781 _25782 _25780) = (term167 _25781 _25782 _25780).
Proof. exact (@lem1668782 (_25780 = (NUMERAL 0)) (term131 _25781 _25782 _25780)). Qed.
Lemma lem1668785 (a : Prop) : (term168 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1668786 (_25781 : real) (_25782 : real) (_25780 : nat) : (term169 _25781 _25782 _25780) = ((real_pow _25781 _25780) = (real_pow _25782 _25780)).
Proof. exact (@lem1668785 ((real_pow _25781 _25780) = (real_pow _25782 _25780))). Qed.
Lemma lem1668787 (_25780 : nat) : (term170 _25780) = (term170 _25780).
Proof. exact (eq_refl (term170 _25780)). Qed.
Lemma lem1668788 (_25781 : real) (_25782 : real) (_25780 : nat) : (term167 _25781 _25782 _25780) = (term140 _25781 _25782 _25780).
Proof. exact (MK_COMB (@lem1668787 _25780) (@lem1668786 _25781 _25782 _25780)). Qed.
Lemma lem1668789 (_25781 : real) (_25782 : real) (_25780 : nat) : (term166 _25781 _25782 _25780) = (term140 _25781 _25782 _25780).
Proof. exact (TRANS (@lem1668783 _25781 _25782 _25780) (@lem1668788 _25781 _25782 _25780)). Qed.
Lemma lem1668790 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1668791 (_25781 : real) (_25782 : real) (_25780 : nat) : (term171 _25781 _25782 _25780) = (term172 _25781 _25782 _25780).
Proof. exact (MK_COMB (@lem1668790) (@lem1668789 _25781 _25782 _25780)). Qed.
Lemma lem1668792 (_25781 : real) (_25782 : real) : ((real_abs _25781) = (real_abs _25782)) = ((real_abs _25781) = (real_abs _25782)).
Proof. exact (eq_refl ((real_abs _25781) = (real_abs _25782))). Qed.
Lemma lem1668793 (_25780 : nat) (_25781 : real) (_25782 : real) : (term163 _25780 _25781 _25782) = (term123 _25780 _25781 _25782).
Proof. exact (MK_COMB (@lem1668791 _25781 _25782 _25780) (@lem1668792 _25781 _25782)). Qed.
Lemma lem1668794 (_25780 : nat) (_25781 : real) (_25782 : real) : (term161 _25781 _25782 _25780) = (term123 _25780 _25781 _25782).
Proof. exact (TRANS (@lem1668780 _25780 _25781 _25782) (@lem1668793 _25780 _25781 _25782)). Qed.
Lemma lem1668796 (n : nat) (x : real) (y : real) (h1 : term34 n) (h2 : term96 n x y) : term140 x y n.
Proof. exact (conj (@lem1668693 n h1) (@lem1668700 n x y h2)). Qed.
Lemma lem1668798 (_25780 : nat) (_25781 : real) (_25782 : real) (h1 : term103) : term123 _25780 _25781 _25782.
Proof. exact (EQ_MP (@lem1668794 _25780 _25781 _25782) (@lem1668777 _25781 _25782 _25780 h1)). Qed.
Lemma lem1668799 (n : nat) (x : real) (y : real) (h1 : term103) : term123 n x y.
Proof. exact (@lem1668798 n x y h1). Qed.
Lemma lem1668802 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : (real_abs x) = (real_abs y).
Proof. exact (@lem1668799 n x y h1 (@lem1668796 n x y h2 h3)). Qed.
Lemma lem1668803 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : term173 x y.
Proof. exact (fun h0 : term151 x y => @lem1668802 n x y h1 h2 h3). Qed.
Lemma lem1668805 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1668806 (x : real) (y : real) : (term173 x y) = ((real_abs x) = (real_abs y)).
Proof. exact (@lem1668805 ((real_abs x) = (real_abs y))). Qed.
Lemma lem1668807 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : (real_abs x) = (real_abs y).
Proof. exact (EQ_MP (@lem1668806 x y) (@lem1668803 n x y h1 h2 h3)). Qed.
Lemma lem1668810 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1668812 (x : real) (y : real) : (term151 x y) = (term174 x y).
Proof. exact (@lem1668810 ((real_abs x) = (real_abs y))). Qed.
Lemma lem1668815 (n : nat) (x : real) (y : real) (h1 : term96 n x y) : term174 x y.
Proof. exact (EQ_MP (@lem1668812 x y) (@lem1668639 n x y h1)). Qed.
Lemma lem1668818 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : False.
Proof. exact (@lem1668815 n x y h3 (@lem1668807 n x y h1 h2 h3)). Qed.
Lemma lem1668819 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : term175.
Proof. exact (fun h0 : ~ False => @lem1668818 n x y h1 h2 h3). Qed.
Lemma lem1668821 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1668822 : term175 = False.
Proof. exact (@lem1668821 False). Qed.
Lemma lem1668823 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : False.
Proof. exact (EQ_MP (@lem1668822) (@lem1668819 n x y h1 h2 h3)). Qed.
Lemma lem1668824 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : (term34 n) = False.
Proof. exact (prop_ext (fun h4 : term34 n => @lem1668823 n x y h1 h2 h3) (fun h4 : False => @lem1668621 n h2)). Qed.
Lemma lem1668825 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : False.
Proof. exact (EQ_MP (@lem1668824 n x y h1 h2 h3) (@lem1668621 n h2)). Qed.
Lemma lem1668826 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : (term34 n) = False.
Proof. exact (prop_ext (fun h4 : term34 n => @lem1668825 n x y h1 h2 h3) (fun h4 : False => @lem1668573 n h2)). Qed.
Lemma lem1668827 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : False.
Proof. exact (EQ_MP (@lem1668826 n x y h1 h2 h3) (@lem1668573 n h2)). Qed.
Lemma lem1668828 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : (term34 n) = False.
Proof. exact (prop_ext (fun h4 : term34 n => @lem1668827 n x y h1 h2 h3) (fun h4 : False => @lem1668573 n h2)). Qed.
Lemma lem1668829 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : False.
Proof. exact (EQ_MP (@lem1668828 n x y h1 h2 h3) (@lem1668573 n h2)). Qed.
Lemma lem1668830 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : (term34 n) = False.
Proof. exact (prop_ext (fun h4 : term34 n => @lem1668829 n x y h1 h2 h3) (fun h4 : False => @lem1668488 n h2)). Qed.
Lemma lem1668831 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : False.
Proof. exact (EQ_MP (@lem1668830 n x y h1 h2 h3) (@lem1668488 n h2)). Qed.
Lemma lem1668832 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : (term34 n) = False.
Proof. exact (prop_ext (fun h4 : term34 n => @lem1668831 n x y h1 h2 h3) (fun h4 : False => @lem1668375 n h2)). Qed.
Lemma lem1668833 (n : nat) (x : real) (y : real) (h1 : term103) (h2 : term34 n) (h3 : term96 n x y) : False.
Proof. exact (EQ_MP (@lem1668832 n x y h1 h2 h3) (@lem1668375 n h2)). Qed.
Lemma lem1668834 (n : nat) (x : real) (y : real) (h1 : term34 n) (h2 : term96 n x y) : term101.
Proof. exact (fun h0 : term103 => @lem1668833 n x y h0 h1 h2). Qed.
Lemma lem1668835 : term101 = term102.
Proof. exact (@lem69 term103). Qed.
Lemma lem1668836 (n : nat) (x : real) (y : real) (h1 : term34 n) (h2 : term96 n x y) : term102.
Proof. exact (EQ_MP (@lem1668835) (@lem1668834 n x y h1 h2)). Qed.
Lemma lem1668837 (x : real) (y : real) (n : nat) (h1 : term34 n) : term106 n x y.
Proof. exact (fun h0 : term96 n x y => @lem1668836 n x y h1 h0). Qed.
Lemma lem1668838 (x : real) (y : real) (n : nat) (h1 : term34 n) : term108 n x y.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem1668837 x y n h1). Qed.
Lemma lem1668839 (n : nat) (x : real) (y : real) : term110 n x y.
Proof. exact (fun h0 : term34 n => @lem1668838 x y n h0). Qed.
Lemma lem1668844 (x : real) (y : real) : term114 x y.
Proof. exact (fun n : nat => @lem1668839 n x y). Qed.
Lemma lem1668849 (y : real) : term118 y.
Proof. exact (fun x : real => @lem1668844 x y). Qed.
Lemma lem1668854 : term122.
Proof. exact (fun y : real => @lem1668849 y). Qed.
Lemma lem1668855 : term121.
Proof. exact (EQ_MP (@lem1668365) (@lem1668854)). Qed.
Lemma lem1668856 (y : real) : term176 y.
Proof. exact (@lem1668855 y). Qed.
Lemma lem1668857 (y : real) : (term176 y) = (term117 y).
Proof. exact (eq_refl (term176 y)). Qed.
Lemma lem1668858 (y : real) : term117 y.
Proof. exact (EQ_MP (@lem1668857 y) (@lem1668856 y)). Qed.
Lemma lem1668859 (y : real) (x : real) : term177 y x.
Proof. exact (@lem1668858 y x). Qed.
Lemma lem1668860 (x : real) (y : real) : (term177 y x) = (term113 x y).
Proof. exact (eq_refl (term177 y x)). Qed.
Lemma lem1668861 (x : real) (y : real) : term113 x y.
Proof. exact (EQ_MP (@lem1668860 x y) (@lem1668859 y x)). Qed.
Lemma lem1668862 (x : real) (y : real) (n : nat) : term178 x y n.
Proof. exact (@lem1668861 x y n). Qed.
Lemma lem1668863 (n : nat) (x : real) (y : real) : (term178 x y n) = (term97 n x y).
Proof. exact (eq_refl (term178 x y n)). Qed.
Lemma lem1668864 (n : nat) (x : real) (y : real) : term97 n x y.
Proof. exact (EQ_MP (@lem1668863 n x y) (@lem1668862 x y n)). Qed.
Lemma lem1668866 (n : nat) (x : real) (y : real) : term97 n x y.
Proof. exact (@lem1668186 n x y (@lem1668864 n x y)). Qed.
Lemma lem1668867 (x : real) (y : real) (n : nat) (h1 : term34 n) : term107 n x y.
Proof. exact (@lem1668866 n x y (@lem1666563 n h1)). Qed.
Lemma lem1668868 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) : term105 n x y.
Proof. exact (@lem1668867 x y n h2 (@lem1668010 n h1)). Qed.
Lemma lem1668869 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) (h3 : term96 n x y) : term101.
Proof. exact (@lem1668868 x y n h1 h2 (@lem1668171 n x y h3)). Qed.
Lemma lem1668870 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) (h3 : term96 n x y) : False.
Proof. exact (@lem1668869 n x y h1 h2 h3 (@lem1653544)). Qed.
Lemma lem1668871 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) (h3 : term96 n x y) : (term96 n x y) = False.
Proof. exact (prop_ext (fun h4 : term96 n x y => @lem1668870 n x y h1 h2 h3) (fun h4 : False => @lem1668171 n x y h3)). Qed.
Lemma lem1668872 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) (h3 : term96 n x y) : False.
Proof. exact (EQ_MP (@lem1668871 n x y h1 h2 h3) (@lem1668171 n x y h3)). Qed.
Lemma lem1668873 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) : term95 n x y.
Proof. exact (fun h0 : term96 n x y => @lem1668872 n x y h1 h2 h0). Qed.
Lemma lem1668874 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) : term94 n x y.
Proof. exact (EQ_MP (@lem1668170 n x y) (@lem1668873 x y n h1 h2)). Qed.
Lemma lem1668880 (x : real) (y : real) : ((real_abs x) = (real_abs y)) = ((term19 x) = (term19 y)).
Proof. exact (EQ_MP (@lem1666537 x y) (@lem1666536 x y)). Qed.
Lemma lem1668883 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1668884 (x : real) (y : real) : (term179 x y) = (term180 x y).
Proof. exact (MK_COMB (@lem1668883) (@lem1668880 x y)). Qed.
Lemma lem1668887 (x : real) (y : real) (n : nat) : ((real_pow x n) = (real_pow y n)) = ((real_pow x n) = (real_pow y n)).
Proof. exact (eq_refl ((real_pow x n) = (real_pow y n))). Qed.
Lemma lem1668888 (x : real) (y : real) (n : nat) : (term181 x y n) = (term182 x y n).
Proof. exact (MK_COMB (@lem1668884 x y) (@lem1668887 x y n)). Qed.
Lemma lem1668893 (x : real) (y : real) (n : nat) : (term182 x y n) = (term181 x y n).
Proof. exact (SYM (@lem1668888 x y n)). Qed.
Lemma lem1668900 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (term15 n).
Proof. exact (EQ_MP (@lem1666531 n) (@lem1666530 n)). Qed.
Lemma lem1668907 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term15 n.
Proof. exact (EQ_MP (@lem1668900 n) (@lem1668010 n h1)). Qed.
Lemma lem1668908 (n : nat) (m : nat) (h1 : n = (term183 m)) : n = (term183 m).
Proof. exact (h1). Qed.
Lemma lem1668909 (x : real) (y : real) : (term184 x y) = (term184 x y).
Proof. exact (eq_refl (term184 x y)). Qed.
Lemma lem1668910 (x : real) (y : real) (n : nat) (m : nat) (h1 : n = (term183 m)) : (term185 x y n) = (term186 x y m).
Proof. exact (MK_COMB (@lem1668909 x y) (@lem1668908 n m h1)). Qed.
Lemma lem1668911 (x : real) (y : real) (m : nat) : (term186 x y m) = ((term187 x m) = (term187 y m)).
Proof. exact (eq_refl (term186 x y m)). Qed.
Lemma lem1668912 (x : real) (y : real) (n : nat) : (term188 x y n) = (term188 x y n).
Proof. exact (eq_refl (term188 x y n)). Qed.
Lemma lem1668913 (n : nat) (x : real) (y : real) (m : nat) : ((term185 x y n) = (term186 x y m)) = ((term185 x y n) = ((term187 x m) = (term187 y m))).
Proof. exact (MK_COMB (@lem1668912 x y n) (@lem1668911 x y m)). Qed.
Lemma lem1668914 (x : real) (y : real) (n : nat) : (term185 x y n) = ((real_pow x n) = (real_pow y n)).
Proof. exact (eq_refl (term185 x y n)). Qed.
Lemma lem1668915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1668916 (x : real) (y : real) (n : nat) : (term188 x y n) = (term50 x y n).
Proof. exact (MK_COMB (@lem1668915) (@lem1668914 x y n)). Qed.
Lemma lem1668917 (x : real) (y : real) (m : nat) : ((term187 x m) = (term187 y m)) = ((term187 x m) = (term187 y m)).
Proof. exact (eq_refl ((term187 x m) = (term187 y m))). Qed.
Lemma lem1668918 (n : nat) (x : real) (y : real) (m : nat) : ((term185 x y n) = ((term187 x m) = (term187 y m))) = (((real_pow x n) = (real_pow y n)) = ((term187 x m) = (term187 y m))).
Proof. exact (MK_COMB (@lem1668916 x y n) (@lem1668917 x y m)). Qed.
Lemma lem1668919 (n : nat) (x : real) (y : real) (m : nat) : ((term185 x y n) = (term186 x y m)) = (((real_pow x n) = (real_pow y n)) = ((term187 x m) = (term187 y m))).
Proof. exact (TRANS (@lem1668913 n x y m) (@lem1668918 n x y m)). Qed.
Lemma lem1668920 (x : real) (y : real) (n : nat) (m : nat) (h1 : n = (term183 m)) : ((real_pow x n) = (real_pow y n)) = ((term187 x m) = (term187 y m)).
Proof. exact (EQ_MP (@lem1668919 n x y m) (@lem1668910 x y n m h1)). Qed.
Lemma lem1668921 (x : real) (y : real) (n : nat) (m : nat) (h1 : n = (term183 m)) : ((term187 x m) = (term187 y m)) = ((real_pow x n) = (real_pow y n)).
Proof. exact (SYM (@lem1668920 x y n m h1)). Qed.
Lemma lem1668922 (x : real) : term189 x.
Proof. exact (@lem1666529 x). Qed.
Lemma lem1668923 (x : real) : (term189 x) = (term9 x).
Proof. exact (eq_refl (term189 x)). Qed.
Lemma lem1668924 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1668923 x) (@lem1668922 x)). Qed.
Lemma lem1668925 (x : real) (m : nat) : term190 x m.
Proof. exact (@lem1668924 x m). Qed.
Lemma lem1668926 (x : real) (m : nat) : (term190 x m) = (term5 x m).
Proof. exact (eq_refl (term190 x m)). Qed.
Lemma lem1668927 (x : real) (m : nat) : term5 x m.
Proof. exact (EQ_MP (@lem1668926 x m) (@lem1668925 x m)). Qed.
Lemma lem1668928 (x : real) (m : nat) (n : nat) : term191 x m n.
Proof. exact (@lem1668927 x m n). Qed.
Lemma lem1668929 (x : real) (m : nat) (n : nat) : (term191 x m n) = ((term1 x m n) = (term0 x m n)).
Proof. exact (eq_refl (term191 x m n)). Qed.
Lemma lem1668947 (x : real) (m : nat) (n : nat) : (term1 x m n) = (term0 x m n).
Proof. exact (EQ_MP (@lem1668929 x m n) (@lem1668928 x m n)). Qed.
Lemma lem1668948 (x : real) (m : nat) : (term187 x m) = (term192 x m).
Proof. exact (@lem1668947 x term193 m). Qed.
Lemma lem1668950 (x : real) (y : real) (h1 : (term19 x) = (term19 y)) : (term19 x) = (term19 y).
Proof. exact (h1). Qed.
Lemma lem1668951 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem1668952 (x : real) (y : real) (h1 : (term19 x) = (term19 y)) : (term194 x) = (term194 y).
Proof. exact (MK_COMB (@lem1668951) (@lem1668950 x y h1)). Qed.
Lemma lem1668953 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1668954 (m : nat) (x : real) (y : real) (h1 : (term19 x) = (term19 y)) : (term192 x m) = (term192 y m).
Proof. exact (MK_COMB (@lem1668952 x y h1) (@lem1668953 m)). Qed.
Lemma lem1668955 (m : nat) (x : real) (y : real) (h1 : (term19 x) = (term19 y)) : (term187 x m) = (term192 y m).
Proof. exact (TRANS (@lem1668948 x m) (@lem1668954 m x y h1)). Qed.
Lemma lem1668956 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1668957 (m : nat) (x : real) (y : real) (h1 : (term19 x) = (term19 y)) : (term195 x m) = (term196 y m).
Proof. exact (MK_COMB (@lem1668956) (@lem1668955 m x y h1)). Qed.
Lemma lem1668959 (x : real) (m : nat) (n : nat) : (term1 x m n) = (term0 x m n).
Proof. exact (EQ_MP (@lem1668929 x m n) (@lem1668928 x m n)). Qed.
Lemma lem1668960 (y : real) (m : nat) : (term187 y m) = (term192 y m).
Proof. exact (@lem1668959 y term193 m). Qed.
Lemma lem1668961 (m : nat) (x : real) (y : real) (h1 : (term19 x) = (term19 y)) : ((term187 x m) = (term187 y m)) = ((term192 y m) = (term192 y m)).
Proof. exact (MK_COMB (@lem1668957 m x y h1) (@lem1668960 y m)). Qed.
Lemma lem1668963 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1668964 (x : real) : (x = x) = True.
Proof. exact (@lem1668963 real x). Qed.
Lemma lem1668965 (y : real) (m : nat) : ((term192 y m) = (term192 y m)) = True.
Proof. exact (@lem1668964 (term192 y m)). Qed.
Lemma lem1668966 (m : nat) (x : real) (y : real) (h1 : (term19 x) = (term19 y)) : ((term187 x m) = (term187 y m)) = True.
Proof. exact (TRANS (@lem1668961 m x y h1) (@lem1668965 y m)). Qed.
Lemma lem1668967 (m : nat) (x : real) (y : real) (h1 : (term19 x) = (term19 y)) : True = ((term187 x m) = (term187 y m)).
Proof. exact (SYM (@lem1668966 m x y h1)). Qed.
Lemma lem1668968 (m : nat) (x : real) (y : real) (h1 : (term19 x) = (term19 y)) : (term187 x m) = (term187 y m).
Proof. exact (EQ_MP (@lem1668967 m x y h1) (@lem0)). Qed.
Lemma lem1668969 (n : nat) (m : nat) (x : real) (y : real) (h1 : n = (term183 m)) (h2 : (term19 x) = (term19 y)) : (real_pow x n) = (real_pow y n).
Proof. exact (EQ_MP (@lem1668921 x y n m h1) (@lem1668968 m x y h2)). Qed.
Lemma lem1668970 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : (term19 x) = (term19 y)) : (real_pow x n) = (real_pow y n).
Proof. exact (ex_elim (@lem1668907 n h1) (fun m : nat => fun h0 : term197 n m => @lem1668969 n m x y h0 h2)). Qed.
Lemma lem1668971 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term182 x y n.
Proof. exact (fun h0 : (term19 x) = (term19 y) => @lem1668970 n x y h1 h0). Qed.
Lemma lem1668972 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term181 x y n.
Proof. exact (EQ_MP (@lem1668893 x y n) (@lem1668971 x y n h1)). Qed.
Lemma lem1668973 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) : term198 x y n.
Proof. exact (conj (@lem1668874 x y n h1 h2) (@lem1668972 x y n h1)). Qed.
Lemma lem1668974 (n : nat) (x : real) (y : real) : (term198 x y n) = (((real_pow x n) = (real_pow y n)) = ((real_abs x) = (real_abs y))).
Proof. exact (@lem32 ((real_pow x n) = (real_pow y n)) ((real_abs x) = (real_abs y))). Qed.
Lemma lem1668977 (x : real) (y : real) (n : nat) (h1 : term27 n) : ((real_pow x n) = (real_pow y n)) = (x = y).
Proof. exact (EQ_MP (@lem1668165 x y n h1) (@lem0)). Qed.
Lemma lem1668978 (x : real) (y : real) (n : nat) (h1 : term27 n) : (term27 n) = (((real_pow x n) = (real_pow y n)) = (x = y)).
Proof. exact (prop_ext (fun h2 : term27 n => @lem1668977 x y n h1) (fun h2 : ((real_pow x n) = (real_pow y n)) = (x = y) => @lem1668027 n h1)). Qed.
Lemma lem1668979 (x : real) (y : real) (n : nat) (h1 : term27 n) : ((real_pow x n) = (real_pow y n)) = (x = y).
Proof. exact (EQ_MP (@lem1668978 x y n h1) (@lem1668027 n h1)). Qed.
Lemma lem1668980 (n : nat) (x : real) (y : real) : term74 n x y.
Proof. exact (fun h0 : term27 n => @lem1668979 x y n h0). Qed.
Lemma lem1668981 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) : ((real_pow x n) = (real_pow y n)) = ((real_abs x) = (real_abs y)).
Proof. exact (EQ_MP (@lem1668974 n x y) (@lem1668973 x y n h1 h2)). Qed.
Lemma lem1668982 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) : (Coq.Arith.PeanoNat.Nat.Even n) = (((real_pow x n) = (real_pow y n)) = ((real_abs x) = (real_abs y))).
Proof. exact (prop_ext (fun h3 : Coq.Arith.PeanoNat.Nat.Even n => @lem1668981 x y n h1 h2) (fun h3 : ((real_pow x n) = (real_pow y n)) = ((real_abs x) = (real_abs y)) => @lem1668010 n h1)). Qed.
Lemma lem1668983 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term34 n) : ((real_pow x n) = (real_pow y n)) = ((real_abs x) = (real_abs y)).
Proof. exact (EQ_MP (@lem1668982 x y n h1 h2) (@lem1668010 n h1)). Qed.
Lemma lem1668984 (x : real) (y : real) (n : nat) (h1 : term34 n) : term78 n x y.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem1668983 x y n h0 h1). Qed.
Lemma lem1668985 (x : real) (y : real) (n : nat) (h1 : term34 n) : term81 n x y.
Proof. exact (conj (@lem1668984 x y n h1) (@lem1668980 n x y)). Qed.
Lemma lem1668986 (x : real) (y : real) (n : nat) (h1 : term34 n) : ((real_pow x n) = (real_pow y n)) = (term63 n x y).
Proof. exact (EQ_MP (@lem1668009 n x y) (@lem1668985 x y n h1)). Qed.
Lemma lem1668987 (x : real) (y : real) (n : nat) (h1 : term34 n) : ((real_pow x n) = (real_pow y n)) = (term58 n x y).
Proof. exact (EQ_MP (@lem1667991 x y n h1) (@lem1668986 x y n h1)). Qed.
Lemma lem1668988 (n : nat) (x : real) (y : real) : ((real_pow x n) = (real_pow y n)) = (term58 n x y).
Proof. exact (or_elim (@lem1666561 n) (fun h0 : n = (NUMERAL 0) => @lem1667298 x y n h0) (fun h0 : term34 n => @lem1668987 x y n h0)). Qed.
Lemma lem1668993 (n : nat) (x : real) : term199 n x.
Proof. exact (fun y : real => @lem1668988 n x y). Qed.
Lemma lem1668998 (n : nat) : term200 n.
Proof. exact (fun x : real => @lem1668993 n x). Qed.
Lemma lem1669003 : term201.
Proof. exact (fun n : nat => @lem1668998 n). Qed.
