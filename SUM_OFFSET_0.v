Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_OFFSET_0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import SUB_ADD_spec.
Require Import SUM_OFFSET_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7223176 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : (term0 m n p f) = (term1 m n f p)) : (term0 m n p f) = (term1 m n f p).
Proof. exact (h1). Qed.
Lemma lem7223177 (m : nat) (n : nat) (f : nat -> real) (p : nat) (h1 : (term0 m n p f) = (term1 m n f p)) : (term1 m n f p) = (term0 m n p f).
Proof. exact (SYM (@lem7223176 m n f p h1)). Qed.
Lemma lem7223178 (m : nat) (n : nat) (p : nat) (f : nat -> real) (h1 : (term1 m n f p) = (term0 m n p f)) : (term1 m n f p) = (term0 m n p f).
Proof. exact (h1). Qed.
Lemma lem7223179 (m : nat) (n : nat) (p : nat) (f : nat -> real) (h1 : (term1 m n f p) = (term0 m n p f)) : (term0 m n p f) = (term1 m n f p).
Proof. exact (SYM (@lem7223178 m n p f h1)). Qed.
Lemma lem7223180 (m : nat) (n : nat) (p : nat) (f : nat -> real) : ((term0 m n p f) = (term1 m n f p)) = ((term1 m n f p) = (term0 m n p f)).
Proof. exact (prop_ext (fun h1 : (term0 m n p f) = (term1 m n f p) => @lem7223177 m n f p h1) (fun h1 : (term1 m n f p) = (term0 m n p f) => @lem7223179 m n p f h1)). Qed.
Lemma lem7223181 (m : nat) (p : nat) (f : nat -> real) : (term2 m f p) = (term3 m p f).
Proof. exact (fun_ext (fun n : nat => @lem7223180 m n p f)). Qed.
Lemma lem7223182 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223183 (m : nat) (p : nat) (f : nat -> real) : (term4 m f p) = (term5 m p f).
Proof. exact (MK_COMB (@lem7223182) (@lem7223181 m p f)). Qed.
Lemma lem7223184 (p : nat) (f : nat -> real) : (term6 f p) = (term7 p f).
Proof. exact (fun_ext (fun m : nat => @lem7223183 m p f)). Qed.
Lemma lem7223185 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223186 (p : nat) (f : nat -> real) : (term8 f p) = (term9 p f).
Proof. exact (MK_COMB (@lem7223185) (@lem7223184 p f)). Qed.
Lemma lem7223187 (p : nat) : (term10 p) = (term11 p).
Proof. exact (fun_ext (fun f : nat -> real => @lem7223186 p f)). Qed.
Lemma lem7223188 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7223189 (p : nat) : (term12 p) = (term13 p).
Proof. exact (MK_COMB (@lem7223188) (@lem7223187 p)). Qed.
Lemma lem7223190 : term14 = term15.
Proof. exact (fun_ext (fun p : nat => @lem7223189 p)). Qed.
Lemma lem7223191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223192 : term16 = term17.
Proof. exact (MK_COMB (@lem7223191) (@lem7223190)). Qed.
Lemma lem7223193 : term17.
Proof. exact (EQ_MP (@lem7223192) (@lem7223171)). Qed.
Lemma lem7223194 (m : nat) : term18 m.
Proof. exact (@lem136494 m). Qed.
Lemma lem7223195 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem7223196 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem7223195 m) (@lem7223194 m)). Qed.
Lemma lem7223197 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem7223196 m n). Qed.
Lemma lem7223198 (n : nat) (m : nat) : (term20 m n) = (term21 n m).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem7223199 (n : nat) (m : nat) : term21 n m.
Proof. exact (EQ_MP (@lem7223198 n m) (@lem7223197 m n)). Qed.
Lemma lem7223200 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem7223201 (n : nat) (m : nat) (h1 : Peano.le n m) : (term22 m n) = m.
Proof. exact (@lem7223199 n m (@lem7223200 n m h1)). Qed.
Lemma lem7223227 : term23.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem7223228 (n : nat) : term24 n.
Proof. exact (@lem7223227 n). Qed.
Lemma lem7223229 (n : nat) : (term24 n) = ((term25 n) = n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem7223231 (p : nat) : term26 p.
Proof. exact (@lem7223193 p). Qed.
Lemma lem7223232 (p : nat) : (term26 p) = (term13 p).
Proof. exact (eq_refl (term26 p)). Qed.
Lemma lem7223233 (p : nat) : term13 p.
Proof. exact (EQ_MP (@lem7223232 p) (@lem7223231 p)). Qed.
Lemma lem7223234 (p : nat) (f : nat -> real) : term27 p f.
Proof. exact (@lem7223233 p f). Qed.
Lemma lem7223235 (p : nat) (f : nat -> real) : (term27 p f) = (term9 p f).
Proof. exact (eq_refl (term27 p f)). Qed.
Lemma lem7223236 (p : nat) (f : nat -> real) : term9 p f.
Proof. exact (EQ_MP (@lem7223235 p f) (@lem7223234 p f)). Qed.
Lemma lem7223237 (p : nat) (f : nat -> real) (m : nat) : term28 p f m.
Proof. exact (@lem7223236 p f m). Qed.
Lemma lem7223238 (m : nat) (p : nat) (f : nat -> real) : (term28 p f m) = (term5 m p f).
Proof. exact (eq_refl (term28 p f m)). Qed.
Lemma lem7223239 (m : nat) (p : nat) (f : nat -> real) : term5 m p f.
Proof. exact (EQ_MP (@lem7223238 m p f) (@lem7223237 p f m)). Qed.
Lemma lem7223240 (m : nat) (p : nat) (f : nat -> real) (n : nat) : term29 m p f n.
Proof. exact (@lem7223239 m p f n). Qed.
Lemma lem7223241 (m : nat) (n : nat) (p : nat) (f : nat -> real) : (term29 m p f n) = ((term1 m n f p) = (term0 m n p f)).
Proof. exact (eq_refl (term29 m p f n)). Qed.
Lemma lem7223258 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term30 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7223259 (p : Prop) (q : Prop) (p' : Prop) : term31 p q p'.
Proof. exact (fun q' : Prop => @lem7223258 p q p' q'). Qed.
Lemma lem7223260 (p : Prop) (q : Prop) : term32 p q.
Proof. exact (fun p' : Prop => @lem7223259 p q p'). Qed.
Lemma lem7223261 (n : nat) (f : nat -> real) (m : nat) : term33 n f m.
Proof. exact (@lem7223260 (Peano.le m n) ((term34 m n f) = (term35 n f m))). Qed.
Lemma lem7223262 (n : nat) (f : nat -> real) (m : nat) (p' : Prop) : term36 n f m p'.
Proof. exact (@lem7223261 n f m p'). Qed.
Lemma lem7223263 (n : nat) (f : nat -> real) (m : nat) (p' : Prop) : (term36 n f m p') = (term37 n f m p').
Proof. exact (eq_refl (term36 n f m p')). Qed.
Lemma lem7223264 (n : nat) (f : nat -> real) (m : nat) (p' : Prop) : term37 n f m p'.
Proof. exact (EQ_MP (@lem7223263 n f m p') (@lem7223262 n f m p')). Qed.
Lemma lem7223265 (n : nat) (f : nat -> real) (m : nat) (p' : Prop) (q' : Prop) : term38 n f m p' q'.
Proof. exact (@lem7223264 n f m p' q'). Qed.
Lemma lem7223266 (n : nat) (f : nat -> real) (m : nat) (p' : Prop) (q' : Prop) : (term38 n f m p' q') = (term39 n f m p' q').
Proof. exact (eq_refl (term38 n f m p' q')). Qed.
Lemma lem7223267 (n : nat) (f : nat -> real) (m : nat) (p' : Prop) (q' : Prop) : term39 n f m p' q'.
Proof. exact (EQ_MP (@lem7223266 n f m p' q') (@lem7223265 n f m p' q')). Qed.
Lemma lem7223268 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem7223269 (f : nat -> real) (m : nat) (n : nat) (q' : Prop) : term40 f m n q'.
Proof. exact (@lem7223267 n f m (Peano.le m n) q'). Qed.
Lemma lem7223270 (f : nat -> real) (m : nat) (n : nat) (q' : Prop) : term41 f m n q'.
Proof. exact (@lem7223269 f m n q' (@lem7223268 m n)). Qed.
Lemma lem7223271 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7223272 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem7223277 (m : nat) (n : nat) (p : nat) (f : nat -> real) : (term1 m n f p) = (term0 m n p f).
Proof. exact (EQ_MP (@lem7223241 m n p f) (@lem7223240 m p f n)). Qed.
Lemma lem7223278 (n : nat) (m : nat) (f : nat -> real) : (term35 n f m) = (term42 n m f).
Proof. exact (@lem7223277 (NUMERAL 0) (Nat.sub n m) m f). Qed.
Lemma lem7223280 (n : nat) : (term25 n) = n.
Proof. exact (EQ_MP (@lem7223229 n) (@lem7223228 n)). Qed.
Lemma lem7223281 (m : nat) : (term25 m) = m.
Proof. exact (@lem7223280 m). Qed.
Lemma lem7223282 : dotdot = dotdot.
Proof. exact (eq_refl dotdot). Qed.
Lemma lem7223283 (m : nat) : (term43 m) = (dotdot m).
Proof. exact (MK_COMB (@lem7223282) (@lem7223281 m)). Qed.
Lemma lem7223285 (n : nat) (m : nat) : term21 n m.
Proof. exact (fun h0 : Peano.le n m => @lem7223201 n m h0). Qed.
Lemma lem7223286 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem7223285 m n). Qed.
Lemma lem7223288 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem7223272 m n) (@lem7223271 m n h1)). Qed.
Lemma lem7223289 (m : nat) (n : nat) (h1 : Peano.le m n) : True = (Peano.le m n).
Proof. exact (SYM (@lem7223288 m n h1)). Qed.
Lemma lem7223290 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem7223289 m n h1) (@lem0)). Qed.
Lemma lem7223291 (m : nat) (n : nat) (h1 : Peano.le m n) : (term22 n m) = n.
Proof. exact (@lem7223286 m n (@lem7223290 m n h1)). Qed.
Lemma lem7223292 (m : nat) (n : nat) (h1 : Peano.le m n) : (term44 n m) = (dotdot m n).
Proof. exact (MK_COMB (@lem7223283 m) (@lem7223291 m n h1)). Qed.
Lemma lem7223293 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7223294 (m : nat) (n : nat) (h1 : Peano.le m n) : (term45 n m) = (term46 m n).
Proof. exact (MK_COMB (@lem7223293) (@lem7223292 m n h1)). Qed.
Lemma lem7223295 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7223296 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term42 n m f) = (term34 m n f).
Proof. exact (MK_COMB (@lem7223294 m n h1) (@lem7223295 f)). Qed.
Lemma lem7223297 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term35 n f m) = (term34 m n f).
Proof. exact (TRANS (@lem7223278 n m f) (@lem7223296 f m n h1)). Qed.
Lemma lem7223298 (m : nat) (n : nat) (f : nat -> real) : (term47 m n f) = (term47 m n f).
Proof. exact (eq_refl (term47 m n f)). Qed.
Lemma lem7223299 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term34 m n f) = (term35 n f m)) = ((term34 m n f) = (term34 m n f)).
Proof. exact (MK_COMB (@lem7223298 m n f) (@lem7223297 f m n h1)). Qed.
Lemma lem7223301 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7223302 (x : real) : (x = x) = True.
Proof. exact (@lem7223301 real x). Qed.
Lemma lem7223303 (m : nat) (n : nat) (f : nat -> real) : ((term34 m n f) = (term34 m n f)) = True.
Proof. exact (@lem7223302 (term34 m n f)). Qed.
Lemma lem7223304 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term34 m n f) = (term35 n f m)) = True.
Proof. exact (TRANS (@lem7223299 f m n h1) (@lem7223303 m n f)). Qed.
Lemma lem7223305 (n : nat) (f : nat -> real) (m : nat) : term48 n f m.
Proof. exact (fun h0 : Peano.le m n => @lem7223304 f m n h0). Qed.
Lemma lem7223306 (f : nat -> real) (m : nat) (n : nat) : term49 f m n.
Proof. exact (@lem7223270 f m n True). Qed.
Lemma lem7223307 (f : nat -> real) (m : nat) (n : nat) : (term50 n f m) = (term51 m n).
Proof. exact (@lem7223306 f m n (@lem7223305 n f m)). Qed.
Lemma lem7223309 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7223310 (m : nat) (n : nat) : (term51 m n) = True.
Proof. exact (@lem7223309 (Peano.le m n)). Qed.
Lemma lem7223311 (n : nat) (f : nat -> real) (m : nat) : (term50 n f m) = True.
Proof. exact (TRANS (@lem7223307 f m n) (@lem7223310 m n)). Qed.
Lemma lem7223312 (f : nat -> real) (m : nat) : (term52 f m) = term53.
Proof. exact (fun_ext (fun n : nat => @lem7223311 n f m)). Qed.
Lemma lem7223313 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223314 (f : nat -> real) (m : nat) : (term54 f m) = term55.
Proof. exact (MK_COMB (@lem7223313) (@lem7223312 f m)). Qed.
Lemma lem7223316 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7223317 (t : Prop) : (term57 t) = t.
Proof. exact (@lem7223316 nat t). Qed.
Lemma lem7223318 : term55 = True.
Proof. exact (@lem7223317 True). Qed.
Lemma lem7223319 (f : nat -> real) (m : nat) : (term54 f m) = True.
Proof. exact (TRANS (@lem7223314 f m) (@lem7223318)). Qed.
Lemma lem7223320 (f : nat -> real) : (term58 f) = term53.
Proof. exact (fun_ext (fun m : nat => @lem7223319 f m)). Qed.
Lemma lem7223321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223322 (f : nat -> real) : (term59 f) = term55.
Proof. exact (MK_COMB (@lem7223321) (@lem7223320 f)). Qed.
Lemma lem7223324 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7223325 (t : Prop) : (term57 t) = t.
Proof. exact (@lem7223324 nat t). Qed.
Lemma lem7223326 : term55 = True.
Proof. exact (@lem7223325 True). Qed.
Lemma lem7223327 (f : nat -> real) : (term59 f) = True.
Proof. exact (TRANS (@lem7223322 f) (@lem7223326)). Qed.
Lemma lem7223328 : term60 = term61.
Proof. exact (fun_ext (fun f : nat -> real => @lem7223327 f)). Qed.
Lemma lem7223329 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7223330 : term62 = term63.
Proof. exact (MK_COMB (@lem7223329) (@lem7223328)). Qed.
Lemma lem7223332 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7223333 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7223332 (nat -> real) t). Qed.
Lemma lem7223334 : term63 = True.
Proof. exact (@lem7223333 True). Qed.
Lemma lem7223335 : term62 = True.
Proof. exact (TRANS (@lem7223330) (@lem7223334)). Qed.
Lemma lem7223336 : True = term62.
Proof. exact (SYM (@lem7223335)). Qed.
Lemma lem7223337 : term62.
Proof. exact (EQ_MP (@lem7223336) (@lem0)). Qed.
