Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1365403_term_abbrevs.
Require Import ADD_EQ_0_spec.
Require Import LE_0_spec.
Require Import REAL_LE_LNEG_spec.
Require Import REAL_LE_NEG2_spec.
Require Import REAL_LE_RNEG_spec.
Require Import thm0_spec.
Require Import thm1340282_spec.
Require Import thm1340339_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm89498_spec.
Lemma lem1365113 (m : nat) : term0 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem1365114 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1365115 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1365114 m) (@lem1365113 m)). Qed.
Lemma lem1365116 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1365115 m n). Qed.
Lemma lem1365117 (m : nat) (n : nat) : (term2 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term3 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1365126 : term4.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem1365127 (m : nat) : term5 m.
Proof. exact (@lem1365126 m). Qed.
Lemma lem1365128 (m : nat) : (term5 m) = ((term6 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem1365130 (n : nat) : term7 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1365131 (n : nat) : (term7 n) = (term8 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1365132 (n : nat) : term8 n.
Proof. exact (EQ_MP (@lem1365131 n) (@lem1365130 n)). Qed.
Lemma lem1365133 (n : nat) : (term8 n) = ((term8 n) = True).
Proof. exact (@lem7 (term8 n)). Qed.
Lemma lem1365135 (m : nat) : term9 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1365136 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1365137 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1365136 m) (@lem1365135 m)). Qed.
Lemma lem1365138 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1365137 m n). Qed.
Lemma lem1365139 (m : nat) (n : nat) : (term11 m n) = ((term12 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1365141 (m : nat) : term13 m.
Proof. exact (@lem1340339 m). Qed.
Lemma lem1365142 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1365143 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem1365142 m) (@lem1365141 m)). Qed.
Lemma lem1365144 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem1365143 m n). Qed.
Lemma lem1365145 (m : nat) (n : nat) : (term15 m n) = ((term16 m n) = (term17 m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem1365147 (x : real) : term18 x.
Proof. exact (@lem1362465 x). Qed.
Lemma lem1365148 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1365149 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem1365148 x) (@lem1365147 x)). Qed.
Lemma lem1365150 (x : real) (y : real) : term20 x y.
Proof. exact (@lem1365149 x y). Qed.
Lemma lem1365151 (x : real) (y : real) : (term20 x y) = ((term21 x y) = (term22 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1365153 (x : real) : term23 x.
Proof. exact (@lem1362225 x). Qed.
Lemma lem1365154 (x : real) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1365155 (x : real) : term24 x.
Proof. exact (EQ_MP (@lem1365154 x) (@lem1365153 x)). Qed.
Lemma lem1365156 (x : real) (y : real) : term25 x y.
Proof. exact (@lem1365155 x y). Qed.
Lemma lem1365157 (x : real) (y : real) : (term25 x y) = ((term26 x y) = (term27 x y)).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1365159 (x : real) : term28 x.
Proof. exact (@lem1362291 x). Qed.
Lemma lem1365160 (x : real) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1365161 (x : real) : term29 x.
Proof. exact (EQ_MP (@lem1365160 x) (@lem1365159 x)). Qed.
Lemma lem1365162 (x : real) (y : real) : term30 x y.
Proof. exact (@lem1365161 x y). Qed.
Lemma lem1365163 (y : real) (x : real) : (term30 x y) = ((term31 x y) = (real_le y x)).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem1365168 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1365169 (m : nat) (n : nat) : ((term32 m n) = True) = (term32 m n).
Proof. exact (@lem1365168 (term32 m n)). Qed.
Lemma lem1365170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365171 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem1365170) (@lem1365169 m n)). Qed.
Lemma lem1365181 (y : real) (x : real) : (term31 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1365163 y x) (@lem1365162 x y)). Qed.
Lemma lem1365182 (n : nat) (m : nat) : (term35 m n) = (term12 n m).
Proof. exact (@lem1365181 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1365183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365184 (n : nat) (m : nat) : (term36 m n) = (term37 n m).
Proof. exact (MK_COMB (@lem1365183) (@lem1365182 n m)). Qed.
Lemma lem1365185 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem1365186 (n : nat) (m : nat) : ((term35 m n) = (Peano.le n m)) = ((term12 n m) = (Peano.le n m)).
Proof. exact (MK_COMB (@lem1365184 n m) (@lem1365185 n m)). Qed.
Lemma lem1365189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365190 (n : nat) (m : nat) : (term38 n m) = (term39 n m).
Proof. exact (MK_COMB (@lem1365189) (@lem1365186 n m)). Qed.
Lemma lem1365199 (m : nat) (n : nat) : ((term40 m n) = (term3 m n)) = ((term40 m n) = (term3 m n)).
Proof. exact (eq_refl ((term40 m n) = (term3 m n))). Qed.
Lemma lem1365200 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (MK_COMB (@lem1365190 n m) (@lem1365199 m n)). Qed.
Lemma lem1365203 (m : nat) (n : nat) : (term39 m n) = (term39 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem1365204 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem1365203 m n) (@lem1365200 m n)). Qed.
Lemma lem1365207 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem1365171 m n) (@lem1365204 m n)). Qed.
Lemma lem1365210 (m : nat) (n : nat) : (term46 m n) = (term45 m n).
Proof. exact (SYM (@lem1365207 m n)). Qed.
Lemma lem1365214 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1365157 x y) (@lem1365156 x y)). Qed.
Lemma lem1365215 (m : nat) (n : nat) : (term32 m n) = (term47 m n).
Proof. exact (@lem1365214 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1365216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365217 (m : nat) (n : nat) : (term34 m n) = (term48 m n).
Proof. exact (MK_COMB (@lem1365216) (@lem1365215 m n)). Qed.
Lemma lem1365229 (x : real) (y : real) : (term21 x y) = (term22 x y).
Proof. exact (EQ_MP (@lem1365151 x y) (@lem1365150 x y)). Qed.
Lemma lem1365230 (m : nat) (n : nat) : (term40 m n) = (term49 m n).
Proof. exact (@lem1365229 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1365231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365232 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem1365231) (@lem1365230 m n)). Qed.
Lemma lem1365239 (m : nat) (n : nat) : (term3 m n) = (term3 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1365240 (m : nat) (n : nat) : ((term40 m n) = (term3 m n)) = ((term49 m n) = (term3 m n)).
Proof. exact (MK_COMB (@lem1365232 m n) (@lem1365239 m n)). Qed.
Lemma lem1365243 (n : nat) (m : nat) : (term39 n m) = (term39 n m).
Proof. exact (eq_refl (term39 n m)). Qed.
Lemma lem1365244 (m : nat) (n : nat) : (term42 m n) = (term52 m n).
Proof. exact (MK_COMB (@lem1365243 n m) (@lem1365240 m n)). Qed.
Lemma lem1365247 (m : nat) (n : nat) : (term39 m n) = (term39 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem1365248 (m : nat) (n : nat) : (term44 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem1365247 m n) (@lem1365244 m n)). Qed.
Lemma lem1365251 (m : nat) (n : nat) : (term46 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem1365217 m n) (@lem1365248 m n)). Qed.
Lemma lem1365254 (m : nat) (n : nat) : (term54 m n) = (term46 m n).
Proof. exact (SYM (@lem1365251 m n)). Qed.
Lemma lem1365258 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem1365145 m n) (@lem1365144 m n)). Qed.
Lemma lem1365259 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem1365260 (m : nat) (n : nat) : (term47 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem1365259) (@lem1365258 m n)). Qed.
Lemma lem1365262 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1365139 m n) (@lem1365138 m n)). Qed.
Lemma lem1365263 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (@lem1365262 (NUMERAL 0) (Nat.add m n)). Qed.
Lemma lem1365265 (n : nat) : (term8 n) = True.
Proof. exact (EQ_MP (@lem1365133 n) (@lem1365132 n)). Qed.
Lemma lem1365266 (m : nat) (n : nat) : (term57 m n) = True.
Proof. exact (@lem1365265 (Nat.add m n)). Qed.
Lemma lem1365267 (m : nat) (n : nat) : (term56 m n) = True.
Proof. exact (TRANS (@lem1365263 m n) (@lem1365266 m n)). Qed.
Lemma lem1365268 (m : nat) (n : nat) : (term47 m n) = True.
Proof. exact (TRANS (@lem1365260 m n) (@lem1365267 m n)). Qed.
Lemma lem1365269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365270 (m : nat) (n : nat) : (term48 m n) = (and True).
Proof. exact (MK_COMB (@lem1365269) (@lem1365268 m n)). Qed.
Lemma lem1365276 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1365139 m n) (@lem1365138 m n)). Qed.
Lemma lem1365277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365278 (m : nat) (n : nat) : (term37 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem1365277) (@lem1365276 m n)). Qed.
Lemma lem1365279 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem1365280 (m : nat) (n : nat) : ((term12 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem1365278 m n) (@lem1365279 m n)). Qed.
Lemma lem1365282 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1365283 (x : Prop) : (x = x) = True.
Proof. exact (@lem1365282 Prop x). Qed.
Lemma lem1365284 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem1365283 (Peano.le m n)). Qed.
Lemma lem1365285 (m : nat) (n : nat) : ((term12 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem1365280 m n) (@lem1365284 m n)). Qed.
Lemma lem1365286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365287 (m : nat) (n : nat) : (term39 m n) = (and True).
Proof. exact (MK_COMB (@lem1365286) (@lem1365285 m n)). Qed.
Lemma lem1365293 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1365139 m n) (@lem1365138 m n)). Qed.
Lemma lem1365294 (n : nat) (m : nat) : (term12 n m) = (Peano.le n m).
Proof. exact (@lem1365293 n m). Qed.
Lemma lem1365295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365296 (n : nat) (m : nat) : (term37 n m) = (term58 n m).
Proof. exact (MK_COMB (@lem1365295) (@lem1365294 n m)). Qed.
Lemma lem1365297 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem1365298 (n : nat) (m : nat) : ((term12 n m) = (Peano.le n m)) = ((Peano.le n m) = (Peano.le n m)).
Proof. exact (MK_COMB (@lem1365296 n m) (@lem1365297 n m)). Qed.
Lemma lem1365300 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1365301 (x : Prop) : (x = x) = True.
Proof. exact (@lem1365300 Prop x). Qed.
Lemma lem1365302 (n : nat) (m : nat) : ((Peano.le n m) = (Peano.le n m)) = True.
Proof. exact (@lem1365301 (Peano.le n m)). Qed.
Lemma lem1365303 (n : nat) (m : nat) : ((term12 n m) = (Peano.le n m)) = True.
Proof. exact (TRANS (@lem1365298 n m) (@lem1365302 n m)). Qed.
Lemma lem1365304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365305 (n : nat) (m : nat) : (term39 n m) = (and True).
Proof. exact (MK_COMB (@lem1365304) (@lem1365303 n m)). Qed.
Lemma lem1365309 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem1365145 m n) (@lem1365144 m n)). Qed.
Lemma lem1365310 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1365311 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem1365310) (@lem1365309 m n)). Qed.
Lemma lem1365312 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem1365313 (m : nat) (n : nat) : (term49 m n) = (term62 m n).
Proof. exact (MK_COMB (@lem1365311 m n) (@lem1365312)). Qed.
Lemma lem1365315 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1365139 m n) (@lem1365138 m n)). Qed.
Lemma lem1365316 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (@lem1365315 (Nat.add m n) (NUMERAL 0)). Qed.
Lemma lem1365317 (m : nat) (n : nat) : (term49 m n) = (term63 m n).
Proof. exact (TRANS (@lem1365313 m n) (@lem1365316 m n)). Qed.
Lemma lem1365318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365319 (m : nat) (n : nat) : (term51 m n) = (term64 m n).
Proof. exact (MK_COMB (@lem1365318) (@lem1365317 m n)). Qed.
Lemma lem1365326 (m : nat) (n : nat) : (term3 m n) = (term3 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1365327 (m : nat) (n : nat) : ((term49 m n) = (term3 m n)) = ((term63 m n) = (term3 m n)).
Proof. exact (MK_COMB (@lem1365319 m n) (@lem1365326 m n)). Qed.
Lemma lem1365330 (m : nat) (n : nat) : (term52 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem1365305 n m) (@lem1365327 m n)). Qed.
Lemma lem1365332 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365333 (m : nat) (n : nat) : (term65 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (@lem1365332 ((term63 m n) = (term3 m n))). Qed.
Lemma lem1365342 (m : nat) (n : nat) : (term52 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (TRANS (@lem1365330 m n) (@lem1365333 m n)). Qed.
Lemma lem1365343 (m : nat) (n : nat) : (term53 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem1365287 m n) (@lem1365342 m n)). Qed.
Lemma lem1365345 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365346 (m : nat) (n : nat) : (term65 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (@lem1365345 ((term63 m n) = (term3 m n))). Qed.
Lemma lem1365355 (m : nat) (n : nat) : (term53 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (TRANS (@lem1365343 m n) (@lem1365346 m n)). Qed.
Lemma lem1365356 (m : nat) (n : nat) : (term54 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem1365270 m n) (@lem1365355 m n)). Qed.
Lemma lem1365358 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365359 (m : nat) (n : nat) : (term65 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (@lem1365358 ((term63 m n) = (term3 m n))). Qed.
Lemma lem1365368 (m : nat) (n : nat) : (term54 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (TRANS (@lem1365356 m n) (@lem1365359 m n)). Qed.
Lemma lem1365369 (m : nat) (n : nat) : ((term63 m n) = (term3 m n)) = (term54 m n).
Proof. exact (SYM (@lem1365368 m n)). Qed.
Lemma lem1365373 (m : nat) : (term6 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1365128 m) (@lem1365127 m)). Qed.
Lemma lem1365374 (m : nat) (n : nat) : (term63 m n) = ((Nat.add m n) = (NUMERAL 0)).
Proof. exact (@lem1365373 (Nat.add m n)). Qed.
Lemma lem1365376 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term3 m n).
Proof. exact (EQ_MP (@lem1365117 m n) (@lem1365116 m n)). Qed.
Lemma lem1365379 (m : nat) (n : nat) : (term63 m n) = (term3 m n).
Proof. exact (TRANS (@lem1365374 m n) (@lem1365376 m n)). Qed.
Lemma lem1365384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365385 (m : nat) (n : nat) : (term64 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem1365384) (@lem1365379 m n)). Qed.
Lemma lem1365392 (m : nat) (n : nat) : (term3 m n) = (term3 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1365393 (m : nat) (n : nat) : ((term63 m n) = (term3 m n)) = ((term3 m n) = (term3 m n)).
Proof. exact (MK_COMB (@lem1365385 m n) (@lem1365392 m n)). Qed.
Lemma lem1365395 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1365396 (x : Prop) : (x = x) = True.
Proof. exact (@lem1365395 Prop x). Qed.
Lemma lem1365397 (m : nat) (n : nat) : ((term3 m n) = (term3 m n)) = True.
Proof. exact (@lem1365396 (term3 m n)). Qed.
Lemma lem1365398 (m : nat) (n : nat) : ((term63 m n) = (term3 m n)) = True.
Proof. exact (TRANS (@lem1365393 m n) (@lem1365397 m n)). Qed.
Lemma lem1365399 (m : nat) (n : nat) : True = ((term63 m n) = (term3 m n)).
Proof. exact (SYM (@lem1365398 m n)). Qed.
Lemma lem1365400 (m : nat) (n : nat) : (term63 m n) = (term3 m n).
Proof. exact (EQ_MP (@lem1365399 m n) (@lem0)). Qed.
Lemma lem1365401 (m : nat) (n : nat) : term54 m n.
Proof. exact (EQ_MP (@lem1365369 m n) (@lem1365400 m n)). Qed.
Lemma lem1365402 (m : nat) (n : nat) : term46 m n.
Proof. exact (EQ_MP (@lem1365254 m n) (@lem1365401 m n)). Qed.
Lemma lem1365403 (m : nat) (n : nat) : term45 m n.
Proof. exact (EQ_MP (@lem1365210 m n) (@lem1365402 m n)). Qed.
