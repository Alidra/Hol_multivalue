Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_CLAUSES_NUMSEG_LT_term_abbrevs.
Require Import FINITE_NUMSEG_LT_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import LT_REFL_spec.
Require Import NUMSEG_CLAUSES_LT_spec.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17784_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem6192144 {A : Type'} (op : type1400 A) : term0 A op.
Proof. exact (@lem5712802 A op). Qed.
Lemma lem6192145 {A : Type'} (op : type1400 A) : (term0 A op) = ((@monoidal A op) = (term1 A op)).
Proof. exact (eq_refl (term0 A op)). Qed.
Lemma lem6192147 (n : nat) : term2 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem6192148 (n : nat) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem6192149 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem6192148 n) (@lem6192147 n)). Qed.
Lemma lem6192150 (n : nat) : term4 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem6192176 {_83095 : Type'} : term5 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem6192177 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (@lem6192176 _83095 p). Qed.
Lemma lem6192178 {_83095 : Type'} (p : _83095 -> Prop) : (term6 _83095 p) = (term7 _83095 p).
Proof. exact (eq_refl (term6 _83095 p)). Qed.
Lemma lem6192179 {_83095 : Type'} (p : _83095 -> Prop) : term7 _83095 p.
Proof. exact (EQ_MP (@lem6192178 _83095 p) (@lem6192177 _83095 p)). Qed.
Lemma lem6192180 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term8 _83095 p x.
Proof. exact (@lem6192179 _83095 p x). Qed.
Lemma lem6192181 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 p x) = ((term9 _83095 x p) = (p x)).
Proof. exact (eq_refl (term8 _83095 p x)). Qed.
Lemma lem6192190 (n : nat) : term10 n.
Proof. exact (@lem4621509 n). Qed.
Lemma lem6192191 (n : nat) : (term10 n) = (term11 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem6192192 (n : nat) : term11 n.
Proof. exact (EQ_MP (@lem6192191 n) (@lem6192190 n)). Qed.
Lemma lem6192193 (n : nat) : (term11 n) = ((term11 n) = True).
Proof. exact (@lem7 (term11 n)). Qed.
Lemma lem6192195 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term12 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6192196 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term12 _120477 _120519 _120521 op) = (term13 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term12 _120477 _120519 _120521 op)). Qed.
Lemma lem6192197 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term13 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6192196 _120477 _120519 _120521 op) (@lem6192195 _120477 _120519 _120521 op)). Qed.
Lemma lem6192198 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6192199 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term14 _120477 _120519 _120521 op.
Proof. exact (@lem6192197 _120477 _120519 _120521 op (@lem6192198 _120519 op h1)). Qed.
Lemma lem6192200 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term15 _120519 _120521 op.
Proof. exact (proj2 (@lem6192199 Prop _120519 _120521 op h1)). Qed.
Lemma lem6192201 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term16 _120519 _120521 op f.
Proof. exact (@lem6192200 _120519 _120521 op h1 f). Qed.
Lemma lem6192202 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term16 _120519 _120521 op f) = (term17 _120519 _120521 op f).
Proof. exact (eq_refl (term16 _120519 _120521 op f)). Qed.
Lemma lem6192203 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term17 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem6192202 _120519 _120521 op f) (@lem6192201 _120519 _120521 f op h1)). Qed.
Lemma lem6192204 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term18 _120519 _120521 op f x.
Proof. exact (@lem6192203 _120519 _120521 f op h1 x). Qed.
Lemma lem6192205 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term18 _120519 _120521 op f x) = (term19 _120519 _120521 x op f).
Proof. exact (eq_refl (term18 _120519 _120521 op f x)). Qed.
Lemma lem6192206 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term19 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem6192205 _120519 _120521 x op f) (@lem6192204 _120519 _120521 f x op h1)). Qed.
Lemma lem6192207 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term20 _120519 _120521 x op f s.
Proof. exact (@lem6192206 _120519 _120521 x f op h1 s). Qed.
Lemma lem6192208 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term20 _120519 _120521 x op f s) = (term21 _120519 _120521 x op s f).
Proof. exact (eq_refl (term20 _120519 _120521 x op f s)). Qed.
Lemma lem6192209 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term21 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6192208 _120519 _120521 x op s f) (@lem6192207 _120519 _120521 x f s op h1)). Qed.
Lemma lem6192210 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem6192211 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term22 _120519 _120521 op x s f) = (term23 _120519 _120521 x op s f).
Proof. exact (@lem6192209 _120519 _120521 x s f op h2 (@lem6192210 _120521 s h1)). Qed.
Lemma lem6192212 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term24 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6192211 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem6192213 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term25 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem6192212 _120519 _120521 x op f s h0). Qed.
Lemma lem6192215 (p : Prop) (q : Prop) (r : Prop) : (term26 p q r) = (term27 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6192220 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term25 _120519 _120521 x op s f) = (term28 _120519 _120521 x op s f).
Proof. exact (@lem6192215 (@FINITE _120521 s) (@monoidal _120519 op) ((term22 _120519 _120521 op x s f) = (term23 _120519 _120521 x op s f))). Qed.
Lemma lem6192222 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term29 _120477 _120519 op.
Proof. exact (proj1 (@lem6192199 _120477 _120519 Prop op h1)). Qed.
Lemma lem6192223 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term30 _120477 _120519 op f.
Proof. exact (@lem6192222 _120477 _120519 op h1 f). Qed.
Lemma lem6192224 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term30 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term30 _120477 _120519 op f)). Qed.
Lemma lem6192225 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem6192224 _120477 _120519 f op) (@lem6192223 _120477 _120519 f op h1)). Qed.
Lemma lem6192231 : term31.
Proof. exact (proj2 (@lem4621002)). Qed.
Lemma lem6192232 (k : nat) : term32 k.
Proof. exact (@lem6192231 k). Qed.
Lemma lem6192233 (k : nat) : (term32 k) = ((term33 k) = (term34 k)).
Proof. exact (eq_refl (term32 k)). Qed.
Lemma lem6192243 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term35 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6192244 (p : Prop) (q : Prop) (p' : Prop) : term36 p q p'.
Proof. exact (fun q' : Prop => @lem6192243 p q p' q'). Qed.
Lemma lem6192245 (p : Prop) (q : Prop) : term37 p q.
Proof. exact (fun p' : Prop => @lem6192244 p q p'). Qed.
Lemma lem6192246 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : term38 _123501 op f.
Proof. exact (@lem6192245 (@monoidal _123501 op) (term39 _123501 op f)). Qed.
Lemma lem6192247 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (p' : Prop) : term40 _123501 op f p'.
Proof. exact (@lem6192246 _123501 op f p'). Qed.
Lemma lem6192248 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (p' : Prop) : (term40 _123501 op f p') = (term41 _123501 op f p').
Proof. exact (eq_refl (term40 _123501 op f p')). Qed.
Lemma lem6192249 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (p' : Prop) : term41 _123501 op f p'.
Proof. exact (EQ_MP (@lem6192248 _123501 op f p') (@lem6192247 _123501 op f p')). Qed.
Lemma lem6192250 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (p' : Prop) (q' : Prop) : term42 _123501 op f p' q'.
Proof. exact (@lem6192249 _123501 op f p' q'). Qed.
Lemma lem6192251 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (p' : Prop) (q' : Prop) : (term42 _123501 op f p' q') = (term43 _123501 op f p' q').
Proof. exact (eq_refl (term42 _123501 op f p' q')). Qed.
Lemma lem6192252 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (p' : Prop) (q' : Prop) : term43 _123501 op f p' q'.
Proof. exact (EQ_MP (@lem6192251 _123501 op f p' q') (@lem6192250 _123501 op f p' q')). Qed.
Lemma lem6192253 {_123501 : Type'} (op : type1400 _123501) : (@monoidal _123501 op) = (@monoidal _123501 op).
Proof. exact (eq_refl (@monoidal _123501 op)). Qed.
Lemma lem6192254 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (q' : Prop) : term44 _123501 f op q'.
Proof. exact (@lem6192252 _123501 op f (@monoidal _123501 op) q'). Qed.
Lemma lem6192255 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (q' : Prop) : term45 _123501 f op q'.
Proof. exact (@lem6192254 _123501 f op q' (@lem6192253 _123501 op)). Qed.
Lemma lem6192256 {_123501 : Type'} (op : type1400 _123501) (h1 : @monoidal _123501 op) : @monoidal _123501 op.
Proof. exact (h1). Qed.
Lemma lem6192257 {_123501 : Type'} (op : type1400 _123501) : (@monoidal _123501 op) = ((@monoidal _123501 op) = True).
Proof. exact (@lem7 (@monoidal _123501 op)). Qed.
Lemma lem6192264 : term46 = (@EMPTY nat).
Proof. exact (proj1 (@lem4621002)). Qed.
Lemma lem6192265 {_123501 : Type'} (op : type1400 _123501) : (@iterate _123501 nat op) = (@iterate _123501 nat op).
Proof. exact (eq_refl (@iterate _123501 nat op)). Qed.
Lemma lem6192266 {_123501 : Type'} (op : type1400 _123501) : (term47 _123501 op) = (@iterate _123501 nat op (@EMPTY nat)).
Proof. exact (MK_COMB (@lem6192265 _123501 op) (@lem6192264)). Qed.
Lemma lem6192267 {_123501 : Type'} (f : nat -> _123501) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6192268 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : (term48 _123501 op f) = (@iterate _123501 nat op (@EMPTY nat) f).
Proof. exact (MK_COMB (@lem6192266 _123501 op) (@lem6192267 _123501 f)). Qed.
Lemma lem6192270 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term49 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6192225 _120477 _120519 f op h0). Qed.
Lemma lem6192271 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) : term50 _123501 f op.
Proof. exact (@lem6192270 nat _123501 f op). Qed.
Lemma lem6192273 {_123501 : Type'} (op : type1400 _123501) (h1 : @monoidal _123501 op) : (@monoidal _123501 op) = True.
Proof. exact (EQ_MP (@lem6192257 _123501 op) (@lem6192256 _123501 op h1)). Qed.
Lemma lem6192274 {_123501 : Type'} (op : type1400 _123501) (h1 : @monoidal _123501 op) : True = (@monoidal _123501 op).
Proof. exact (SYM (@lem6192273 _123501 op h1)). Qed.
Lemma lem6192275 {_123501 : Type'} (op : type1400 _123501) (h1 : @monoidal _123501 op) : @monoidal _123501 op.
Proof. exact (EQ_MP (@lem6192274 _123501 op h1) (@lem0)). Qed.
Lemma lem6192276 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (@iterate _123501 nat op (@EMPTY nat) f) = (@neutral _123501 op).
Proof. exact (@lem6192271 _123501 f op (@lem6192275 _123501 op h1)). Qed.
Lemma lem6192277 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term48 _123501 op f) = (@neutral _123501 op).
Proof. exact (TRANS (@lem6192268 _123501 op f) (@lem6192276 _123501 f op h1)). Qed.
Lemma lem6192278 {_123501 : Type'} : (@eq _123501) = (@eq _123501).
Proof. exact (eq_refl (@eq _123501)). Qed.
Lemma lem6192279 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term51 _123501 op f) = (term52 _123501 op).
Proof. exact (MK_COMB (@lem6192278 _123501) (@lem6192277 _123501 f op h1)). Qed.
Lemma lem6192280 {_123501 : Type'} (op : type1400 _123501) : (@neutral _123501 op) = (@neutral _123501 op).
Proof. exact (eq_refl (@neutral _123501 op)). Qed.
Lemma lem6192281 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : ((term48 _123501 op f) = (@neutral _123501 op)) = ((@neutral _123501 op) = (@neutral _123501 op)).
Proof. exact (MK_COMB (@lem6192279 _123501 f op h1) (@lem6192280 _123501 op)). Qed.
Lemma lem6192283 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6192284 {_123501 : Type'} (x : _123501) : (x = x) = True.
Proof. exact (@lem6192283 _123501 x). Qed.
Lemma lem6192285 {_123501 : Type'} (op : type1400 _123501) : ((@neutral _123501 op) = (@neutral _123501 op)) = True.
Proof. exact (@lem6192284 _123501 (@neutral _123501 op)). Qed.
Lemma lem6192286 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : ((term48 _123501 op f) = (@neutral _123501 op)) = True.
Proof. exact (TRANS (@lem6192281 _123501 f op h1) (@lem6192285 _123501 op)). Qed.
Lemma lem6192287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6192288 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term53 _123501 f op) = (and True).
Proof. exact (MK_COMB (@lem6192287) (@lem6192286 _123501 f op h1)). Qed.
Lemma lem6192296 (k : nat) : (term33 k) = (term34 k).
Proof. exact (EQ_MP (@lem6192233 k) (@lem6192232 k)). Qed.
Lemma lem6192301 {_123501 : Type'} (op : type1400 _123501) : (@iterate _123501 nat op) = (@iterate _123501 nat op).
Proof. exact (eq_refl (@iterate _123501 nat op)). Qed.
Lemma lem6192302 {_123501 : Type'} (op : type1400 _123501) (k : nat) : (term54 _123501 op k) = (term55 _123501 op k).
Proof. exact (MK_COMB (@lem6192301 _123501 op) (@lem6192296 k)). Qed.
Lemma lem6192307 {_123501 : Type'} (f : nat -> _123501) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6192308 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) : (term56 _123501 op k f) = (term57 _123501 op k f).
Proof. exact (MK_COMB (@lem6192302 _123501 op k) (@lem6192307 _123501 f)). Qed.
Lemma lem6192310 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term28 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6192220 _120519 _120521 x op s f) (@lem6192213 _120519 _120521 x op s f)). Qed.
Lemma lem6192311 {_123501 : Type'} (x : nat) (op : type1400 _123501) (s : nat -> Prop) (f : nat -> _123501) : term58 _123501 x op s f.
Proof. exact (@lem6192310 _123501 nat x op s f). Qed.
Lemma lem6192312 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) : term59 _123501 op k f.
Proof. exact (@lem6192311 _123501 k op (term60 k) f). Qed.
Lemma lem6192316 (n : nat) : (term11 n) = True.
Proof. exact (EQ_MP (@lem6192193 n) (@lem6192192 n)). Qed.
Lemma lem6192317 (k : nat) : (term11 k) = True.
Proof. exact (@lem6192316 k). Qed.
Lemma lem6192318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6192319 (k : nat) : (term61 k) = (and True).
Proof. exact (MK_COMB (@lem6192318) (@lem6192317 k)). Qed.
Lemma lem6192321 {_123501 : Type'} (op : type1400 _123501) (h1 : @monoidal _123501 op) : (@monoidal _123501 op) = True.
Proof. exact (EQ_MP (@lem6192257 _123501 op) (@lem6192256 _123501 op h1)). Qed.
Lemma lem6192322 {_123501 : Type'} (k : nat) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term62 _123501 k op) = (True /\ True).
Proof. exact (MK_COMB (@lem6192319 k) (@lem6192321 _123501 op h1)). Qed.
Lemma lem6192324 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6192325 : (True /\ True) = True.
Proof. exact (@lem6192324 True). Qed.
Lemma lem6192326 {_123501 : Type'} (k : nat) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term62 _123501 k op) = True.
Proof. exact (TRANS (@lem6192322 _123501 k op h1) (@lem6192325)). Qed.
Lemma lem6192327 {_123501 : Type'} (k : nat) (op : type1400 _123501) (h1 : @monoidal _123501 op) : True = (term62 _123501 k op).
Proof. exact (SYM (@lem6192326 _123501 k op h1)). Qed.
Lemma lem6192328 {_123501 : Type'} (k : nat) (op : type1400 _123501) (h1 : @monoidal _123501 op) : term62 _123501 k op.
Proof. exact (EQ_MP (@lem6192327 _123501 k op h1) (@lem0)). Qed.
Lemma lem6192329 {_123501 : Type'} (k : nat) (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term57 _123501 op k f) = (term63 _123501 op k f).
Proof. exact (@lem6192312 _123501 op k f (@lem6192328 _123501 k op h1)). Qed.
Lemma lem6192387 {_123501 : Type'} (k : nat) (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term56 _123501 op k f) = (term63 _123501 op k f).
Proof. exact (TRANS (@lem6192308 _123501 op k f) (@lem6192329 _123501 k f op h1)). Qed.
Lemma lem6192388 {_123501 : Type'} : (@eq _123501) = (@eq _123501).
Proof. exact (eq_refl (@eq _123501)). Qed.
Lemma lem6192389 {_123501 : Type'} (k : nat) (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term64 _123501 op k f) = (term65 _123501 op k f).
Proof. exact (MK_COMB (@lem6192388 _123501) (@lem6192387 _123501 k f op h1)). Qed.
Lemma lem6192451 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (k : nat) : (term66 _123501 op f k) = (term66 _123501 op f k).
Proof. exact (eq_refl (term66 _123501 op f k)). Qed.
Lemma lem6192452 {_123501 : Type'} (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : @monoidal _123501 op) : ((term56 _123501 op k f) = (term66 _123501 op f k)) = ((term63 _123501 op k f) = (term66 _123501 op f k)).
Proof. exact (MK_COMB (@lem6192389 _123501 k f op h1) (@lem6192451 _123501 op f k)). Qed.
Lemma lem6192516 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term67 _123501 op f) = (term68 _123501 op f).
Proof. exact (fun_ext (fun k : nat => @lem6192452 _123501 f k op h1)). Qed.
Lemma lem6192580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6192581 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term69 _123501 op f) = (term70 _123501 op f).
Proof. exact (MK_COMB (@lem6192580) (@lem6192516 _123501 f op h1)). Qed.
Lemma lem6192649 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term39 _123501 op f) = (term71 _123501 op f).
Proof. exact (MK_COMB (@lem6192288 _123501 f op h1) (@lem6192581 _123501 f op h1)). Qed.
Lemma lem6192651 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6192652 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : (term71 _123501 op f) = (term70 _123501 op f).
Proof. exact (@lem6192651 (term70 _123501 op f)). Qed.
Lemma lem6192720 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) (h1 : @monoidal _123501 op) : (term39 _123501 op f) = (term70 _123501 op f).
Proof. exact (TRANS (@lem6192649 _123501 f op h1) (@lem6192652 _123501 op f)). Qed.
Lemma lem6192721 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : term72 _123501 op f.
Proof. exact (fun h0 : @monoidal _123501 op => @lem6192720 _123501 f op h0). Qed.
Lemma lem6192722 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : term73 _123501 op f.
Proof. exact (@lem6192255 _123501 f op (term70 _123501 op f)). Qed.
Lemma lem6192723 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : (term74 _123501 op f) = (term75 _123501 op f).
Proof. exact (@lem6192722 _123501 op f (@lem6192721 _123501 op f)). Qed.
Lemma lem6192881 {_123501 : Type'} (f : nat -> _123501) : (term76 _123501 f) = (term77 _123501 f).
Proof. exact (fun_ext (fun op : type1400 _123501 => @lem6192723 _123501 op f)). Qed.
Lemma lem6193039 {_123501 : Type'} : (@all (_123501 -> _123501 -> _123501)) = (@all (_123501 -> _123501 -> _123501)).
Proof. exact (eq_refl (@all (_123501 -> _123501 -> _123501))). Qed.
Lemma lem6193040 {_123501 : Type'} (f : nat -> _123501) : (term78 _123501 f) = (term79 _123501 f).
Proof. exact (MK_COMB (@lem6193039 _123501) (@lem6192881 _123501 f)). Qed.
Lemma lem6193202 {_123501 : Type'} (f : nat -> _123501) : (term79 _123501 f) = (term78 _123501 f).
Proof. exact (SYM (@lem6193040 _123501 f)). Qed.
Lemma lem6193210 {A : Type'} (op : type1400 A) : (@monoidal A op) = (term1 A op).
Proof. exact (EQ_MP (@lem6192145 A op) (@lem6192144 A op)). Qed.
Lemma lem6193211 {_123501 : Type'} (op : type1400 _123501) : (@monoidal _123501 op) = (term1 _123501 op).
Proof. exact (@lem6193210 _123501 op). Qed.
Lemma lem6193246 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6193247 {_123501 : Type'} (op : type1400 _123501) : (term80 _123501 op) = (term81 _123501 op).
Proof. exact (MK_COMB (@lem6193246) (@lem6193211 _123501 op)). Qed.
Lemma lem6193255 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term9 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6192181 _83095 p x) (@lem6192180 _83095 p x)). Qed.
Lemma lem6193256 (p : nat -> Prop) (x : nat) : (term82 x p) = (p x).
Proof. exact (@lem6193255 nat p x). Qed.
Lemma lem6193257 (k : nat) : (term83 k) = (term84 k).
Proof. exact (@lem6193256 (term85 k) k). Qed.
Lemma lem6193258 (i : nat) (k : nat) : (term86 k i) = (Peano.lt i k).
Proof. exact (eq_refl (term86 k i)). Qed.
Lemma lem6193259 (GEN_PVAR_181 : nat) : (@SETSPEC nat GEN_PVAR_181) = (@SETSPEC nat GEN_PVAR_181).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_181)). Qed.
Lemma lem6193260 (GEN_PVAR_181 : nat) (i : nat) (k : nat) : (term87 GEN_PVAR_181 k i) = (term88 GEN_PVAR_181 i k).
Proof. exact (MK_COMB (@lem6193259 GEN_PVAR_181) (@lem6193258 i k)). Qed.
Lemma lem6193261 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6193262 (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term89 GEN_PVAR_181 k i) = (term90 GEN_PVAR_181 k i).
Proof. exact (MK_COMB (@lem6193260 GEN_PVAR_181 i k) (@lem6193261 i)). Qed.
Lemma lem6193263 (GEN_PVAR_181 : nat) (k : nat) : (term91 GEN_PVAR_181 k) = (term92 GEN_PVAR_181 k).
Proof. exact (fun_ext (fun i : nat => @lem6193262 GEN_PVAR_181 k i)). Qed.
Lemma lem6193264 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6193265 (GEN_PVAR_181 : nat) (k : nat) : (term93 GEN_PVAR_181 k) = (term94 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6193264) (@lem6193263 GEN_PVAR_181 k)). Qed.
Lemma lem6193266 (k : nat) : (term95 k) = (term96 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6193265 GEN_PVAR_181 k)). Qed.
Lemma lem6193267 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem6193268 (k : nat) : (term97 k) = (term60 k).
Proof. exact (MK_COMB (@lem6193267) (@lem6193266 k)). Qed.
Lemma lem6193269 (k : nat) : (@IN nat k) = (@IN nat k).
Proof. exact (eq_refl (@IN nat k)). Qed.
Lemma lem6193270 (k : nat) : (term83 k) = (term98 k).
Proof. exact (MK_COMB (@lem6193269 k) (@lem6193268 k)). Qed.
Lemma lem6193271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6193272 (k : nat) : (term99 k) = (term100 k).
Proof. exact (MK_COMB (@lem6193271) (@lem6193270 k)). Qed.
Lemma lem6193273 (k : nat) : (term84 k) = (Peano.lt k k).
Proof. exact (eq_refl (term84 k)). Qed.
Lemma lem6193274 (k : nat) : ((term83 k) = (term84 k)) = ((term98 k) = (Peano.lt k k)).
Proof. exact (MK_COMB (@lem6193272 k) (@lem6193273 k)). Qed.
Lemma lem6193275 (k : nat) : (term98 k) = (Peano.lt k k).
Proof. exact (EQ_MP (@lem6193274 k) (@lem6193257 k)). Qed.
Lemma lem6193277 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem6192150 n (@lem6192149 n)). Qed.
Lemma lem6193278 (k : nat) : (Peano.lt k k) = False.
Proof. exact (@lem6193277 k). Qed.
Lemma lem6193279 (k : nat) : (term98 k) = False.
Proof. exact (TRANS (@lem6193275 k) (@lem6193278 k)). Qed.
Lemma lem6193280 {_123501 : Type'} : (@COND _123501) = (@COND _123501).
Proof. exact (eq_refl (@COND _123501)). Qed.
Lemma lem6193281 {_123501 : Type'} (k : nat) : (term101 _123501 k) = (@COND _123501 False).
Proof. exact (MK_COMB (@lem6193280 _123501) (@lem6193279 k)). Qed.
Lemma lem6193288 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) : (term102 _123501 op k f) = (term102 _123501 op k f).
Proof. exact (eq_refl (term102 _123501 op k f)). Qed.
Lemma lem6193289 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) : (term103 _123501 op k f) = (term104 _123501 op k f).
Proof. exact (MK_COMB (@lem6193281 _123501 k) (@lem6193288 _123501 op k f)). Qed.
Lemma lem6193296 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) : (term105 _123501 op k f) = (term105 _123501 op k f).
Proof. exact (eq_refl (term105 _123501 op k f)). Qed.
Lemma lem6193297 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) : (term63 _123501 op k f) = (term106 _123501 op k f).
Proof. exact (MK_COMB (@lem6193289 _123501 op k f) (@lem6193296 _123501 op k f)). Qed.
Lemma lem6193299 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6193300 {_123501 : Type'} (t1 : _123501) (t2 : _123501) : (@COND _123501 False t1 t2) = t2.
Proof. exact (@lem6193299 _123501 t1 t2). Qed.
Lemma lem6193301 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) : (term106 _123501 op k f) = (term105 _123501 op k f).
Proof. exact (@lem6193300 _123501 (term102 _123501 op k f) (term105 _123501 op k f)). Qed.
Lemma lem6193308 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) : (term63 _123501 op k f) = (term105 _123501 op k f).
Proof. exact (TRANS (@lem6193297 _123501 op k f) (@lem6193301 _123501 op k f)). Qed.
Lemma lem6193309 {_123501 : Type'} : (@eq _123501) = (@eq _123501).
Proof. exact (eq_refl (@eq _123501)). Qed.
Lemma lem6193310 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) : (term65 _123501 op k f) = (term107 _123501 op k f).
Proof. exact (MK_COMB (@lem6193309 _123501) (@lem6193308 _123501 op k f)). Qed.
Lemma lem6193317 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (k : nat) : (term66 _123501 op f k) = (term66 _123501 op f k).
Proof. exact (eq_refl (term66 _123501 op f k)). Qed.
Lemma lem6193318 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (k : nat) : ((term63 _123501 op k f) = (term66 _123501 op f k)) = ((term105 _123501 op k f) = (term66 _123501 op f k)).
Proof. exact (MK_COMB (@lem6193310 _123501 op k f) (@lem6193317 _123501 op f k)). Qed.
Lemma lem6193321 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : (term68 _123501 op f) = (term108 _123501 op f).
Proof. exact (fun_ext (fun k : nat => @lem6193318 _123501 op f k)). Qed.
Lemma lem6193322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193323 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : (term70 _123501 op f) = (term109 _123501 op f).
Proof. exact (MK_COMB (@lem6193322) (@lem6193321 _123501 op f)). Qed.
Lemma lem6193328 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : (term75 _123501 op f) = (term110 _123501 op f).
Proof. exact (MK_COMB (@lem6193247 _123501 op) (@lem6193323 _123501 op f)). Qed.
Lemma lem6193331 {_123501 : Type'} (f : nat -> _123501) : (term77 _123501 f) = (term111 _123501 f).
Proof. exact (fun_ext (fun op : type1400 _123501 => @lem6193328 _123501 op f)). Qed.
Lemma lem6193332 {_123501 : Type'} : (@all (_123501 -> _123501 -> _123501)) = (@all (_123501 -> _123501 -> _123501)).
Proof. exact (eq_refl (@all (_123501 -> _123501 -> _123501))). Qed.
Lemma lem6193333 {_123501 : Type'} (f : nat -> _123501) : (term79 _123501 f) = (term112 _123501 f).
Proof. exact (MK_COMB (@lem6193332 _123501) (@lem6193331 _123501 f)). Qed.
Lemma lem6193338 {_123501 : Type'} (f : nat -> _123501) : (term112 _123501 f) = (term79 _123501 f).
Proof. exact (SYM (@lem6193333 _123501 f)). Qed.
Lemma lem6193340 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6193341 {_123501 : Type'} (f : nat -> _123501) : (term112 _123501 f) = (term114 _123501 f).
Proof. exact (@lem6193340 (term112 _123501 f)). Qed.
Lemma lem6193342 {_123501 : Type'} (f : nat -> _123501) : (term114 _123501 f) = (term112 _123501 f).
Proof. exact (SYM (@lem6193341 _123501 f)). Qed.
Lemma lem6193343 {_123501 : Type'} (f : nat -> _123501) (h1 : term115 _123501 f) : term115 _123501 f.
Proof. exact (h1). Qed.
Lemma lem6193346 {_123501 : Type'} (f : nat -> _123501) (h1 : term114 _123501 f) : term114 _123501 f.
Proof. exact (h1). Qed.
Lemma lem6193347 {_123501 : Type'} (f : nat -> _123501) : term116 _123501 f.
Proof. exact (fun h0 : term114 _123501 f => @lem6193346 _123501 f h0). Qed.
Lemma lem6193348 {_123501 : Type'} (f : nat -> _123501) (h1 : term116 _123501 f) : term116 _123501 f.
Proof. exact (h1). Qed.
Lemma lem6193349 {_123501 : Type'} (f : nat -> _123501) (h1 : term114 _123501 f) : term114 _123501 f.
Proof. exact (h1). Qed.
Lemma lem6193350 {_123501 : Type'} (f : nat -> _123501) (h1 : term114 _123501 f) (h2 : term116 _123501 f) : term114 _123501 f.
Proof. exact (@lem6193348 _123501 f h2 (@lem6193349 _123501 f h1)). Qed.
Lemma lem6193351 {_123501 : Type'} (f : nat -> _123501) (h1 : term114 _123501 f) : term117 _123501 f.
Proof. exact (fun h0 : term116 _123501 f => @lem6193350 _123501 f h1 h0). Qed.
Lemma lem6193352 {_123501 : Type'} (f : nat -> _123501) (h1 : term116 _123501 f) : term116 _123501 f.
Proof. exact (h1). Qed.
Lemma lem6193353 {_123501 : Type'} (f : nat -> _123501) (h1 : term114 _123501 f) (h2 : term116 _123501 f) : term114 _123501 f.
Proof. exact (@lem6193351 _123501 f h1 (@lem6193352 _123501 f h2)). Qed.
Lemma lem6193354 {_123501 : Type'} (f : nat -> _123501) (h1 : term116 _123501 f) : term116 _123501 f.
Proof. exact (fun h0 : term114 _123501 f => @lem6193353 _123501 f h0 h1). Qed.
Lemma lem6193355 {_123501 : Type'} (f : nat -> _123501) : term118 _123501 f.
Proof. exact (fun h0 : term116 _123501 f => @lem6193354 _123501 f h0). Qed.
Lemma lem6193358 {_123501 : Type'} (f : nat -> _123501) : term116 _123501 f.
Proof. exact (@lem6193355 _123501 f (@lem6193347 _123501 f)). Qed.
Lemma lem6193359 {_123501 : Type'} (f : nat -> _123501) : term116 _123501 f.
Proof. exact (@lem6193358 _123501 f). Qed.
Lemma lem6193365 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6193366 {_123501 : Type'} (f : nat -> _123501) : (term114 _123501 f) = (term119 _123501 f).
Proof. exact (@lem6193365 (term115 _123501 f)). Qed.
Lemma lem6193368 (t : Prop) : (term120 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6193369 {_123501 : Type'} (f : nat -> _123501) : (term119 _123501 f) = (term112 _123501 f).
Proof. exact (@lem6193368 (term112 _123501 f)). Qed.
Lemma lem6193374 {_123501 : Type'} (f : nat -> _123501) : (term114 _123501 f) = (term112 _123501 f).
Proof. exact (TRANS (@lem6193366 _123501 f) (@lem6193369 _123501 f)). Qed.
Lemma lem6193417 {_123501 : Type'} : (term121 _123501) = (term122 _123501).
Proof. exact (fun_ext (fun f : nat -> _123501 => @lem6193374 _123501 f)). Qed.
Lemma lem6193418 {_123501 : Type'} : (@all (nat -> _123501)) = (@all (nat -> _123501)).
Proof. exact (eq_refl (@all (nat -> _123501))). Qed.
Lemma lem6193425 {_123501 : Type'} : (term123 _123501) = (term124 _123501).
Proof. exact (MK_COMB (@lem6193418 _123501) (@lem6193417 _123501)). Qed.
Lemma lem6193426 (_78901 : type1605) (h1 : _78901 = term125) : _78901 = term125.
Proof. exact (h1). Qed.
Lemma lem6193427 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6193428 (k : nat) (_78901 : type1605) (h1 : _78901 = term125) : (_78901 k) = (term126 k).
Proof. exact (MK_COMB (@lem6193426 _78901 h1) (@lem6193427 k)). Qed.
Lemma lem6193429 (k : nat) : (term126 k) = (term96 k).
Proof. exact (eq_refl (term126 k)). Qed.
Lemma lem6193430 (_78901 : type1605) (k : nat) : (term127 _78901 k) = (term127 _78901 k).
Proof. exact (eq_refl (term127 _78901 k)). Qed.
Lemma lem6193431 (_78901 : type1605) (k : nat) : ((_78901 k) = (term126 k)) = ((_78901 k) = (term96 k)).
Proof. exact (MK_COMB (@lem6193430 _78901 k) (@lem6193429 k)). Qed.
Lemma lem6193432 (k : nat) (_78901 : type1605) (h1 : _78901 = term125) : (_78901 k) = (term96 k).
Proof. exact (EQ_MP (@lem6193431 _78901 k) (@lem6193428 k _78901 h1)). Qed.
Lemma lem6193436 {_123501 : Type'} (f : nat -> _123501) (k : nat) : (f k) = (f k).
Proof. exact (eq_refl (f k)). Qed.
Lemma lem6193437 {_123501 : Type'} (f : nat -> _123501) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6193439 (k : nat) (_78901 : type1605) (h1 : _78901 = term125) : (term96 k) = (_78901 k).
Proof. exact (SYM (@lem6193432 k _78901 h1)). Qed.
Lemma lem6193440 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem6193441 (k : nat) (_78901 : type1605) (h1 : _78901 = term125) : (term60 k) = (term128 _78901 k).
Proof. exact (MK_COMB (@lem6193440) (@lem6193439 k _78901 h1)). Qed.
Lemma lem6193444 {_123501 : Type'} (op : type1400 _123501) : (@iterate _123501 nat op) = (@iterate _123501 nat op).
Proof. exact (eq_refl (@iterate _123501 nat op)). Qed.
Lemma lem6193445 {_123501 : Type'} (op : type1400 _123501) (k : nat) (_78901 : type1605) (h1 : _78901 = term125) : (term129 _123501 op k) = (term130 _123501 op _78901 k).
Proof. exact (MK_COMB (@lem6193444 _123501 op) (@lem6193441 k _78901 h1)). Qed.
Lemma lem6193446 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) (_78901 : type1605) (h1 : _78901 = term125) : (term102 _123501 op k f) = (term131 _123501 op _78901 k f).
Proof. exact (MK_COMB (@lem6193445 _123501 op k _78901 h1) (@lem6193437 _123501 f)). Qed.
Lemma lem6193447 {_123501 : Type'} (op : type1400 _123501) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6193448 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) (_78901 : type1605) (h1 : _78901 = term125) : (term132 _123501 op k f) = (term133 _123501 op _78901 k f).
Proof. exact (MK_COMB (@lem6193447 _123501 op) (@lem6193446 _123501 op k f _78901 h1)). Qed.
Lemma lem6193449 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (k : nat) (_78901 : type1605) (h1 : _78901 = term125) : (term66 _123501 op f k) = (term134 _123501 op _78901 f k).
Proof. exact (MK_COMB (@lem6193448 _123501 op k f _78901 h1) (@lem6193436 _123501 f k)). Qed.
Lemma lem6193450 {_123501 : Type'} (f : nat -> _123501) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6193452 (k : nat) (_78901 : type1605) (h1 : _78901 = term125) : (term96 k) = (_78901 k).
Proof. exact (SYM (@lem6193432 k _78901 h1)). Qed.
Lemma lem6193453 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem6193454 (k : nat) (_78901 : type1605) (h1 : _78901 = term125) : (term60 k) = (term128 _78901 k).
Proof. exact (MK_COMB (@lem6193453) (@lem6193452 k _78901 h1)). Qed.
Lemma lem6193457 {_123501 : Type'} (op : type1400 _123501) : (@iterate _123501 nat op) = (@iterate _123501 nat op).
Proof. exact (eq_refl (@iterate _123501 nat op)). Qed.
Lemma lem6193458 {_123501 : Type'} (op : type1400 _123501) (k : nat) (_78901 : type1605) (h1 : _78901 = term125) : (term129 _123501 op k) = (term130 _123501 op _78901 k).
Proof. exact (MK_COMB (@lem6193457 _123501 op) (@lem6193454 k _78901 h1)). Qed.
Lemma lem6193459 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) (_78901 : type1605) (h1 : _78901 = term125) : (term102 _123501 op k f) = (term131 _123501 op _78901 k f).
Proof. exact (MK_COMB (@lem6193458 _123501 op k _78901 h1) (@lem6193450 _123501 f)). Qed.
Lemma lem6193464 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (k : nat) : (term135 _123501 op f k) = (term135 _123501 op f k).
Proof. exact (eq_refl (term135 _123501 op f k)). Qed.
Lemma lem6193465 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) (_78901 : type1605) (h1 : _78901 = term125) : (term105 _123501 op k f) = (term136 _123501 op _78901 k f).
Proof. exact (MK_COMB (@lem6193464 _123501 op f k) (@lem6193459 _123501 op k f _78901 h1)). Qed.
Lemma lem6193466 {_123501 : Type'} : (@eq _123501) = (@eq _123501).
Proof. exact (eq_refl (@eq _123501)). Qed.
Lemma lem6193467 {_123501 : Type'} (op : type1400 _123501) (k : nat) (f : nat -> _123501) (_78901 : type1605) (h1 : _78901 = term125) : (term107 _123501 op k f) = (term137 _123501 op _78901 k f).
Proof. exact (MK_COMB (@lem6193466 _123501) (@lem6193465 _123501 op k f _78901 h1)). Qed.
Lemma lem6193468 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (k : nat) (_78901 : type1605) (h1 : _78901 = term125) : ((term105 _123501 op k f) = (term66 _123501 op f k)) = ((term136 _123501 op _78901 k f) = (term134 _123501 op _78901 f k)).
Proof. exact (MK_COMB (@lem6193467 _123501 op k f _78901 h1) (@lem6193449 _123501 op f k _78901 h1)). Qed.
Lemma lem6193469 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (_78901 : type1605) (h1 : _78901 = term125) : (term108 _123501 op f) = (term138 _123501 op _78901 f).
Proof. exact (fun_ext (fun k : nat => @lem6193468 _123501 op f k _78901 h1)). Qed.
Lemma lem6193470 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193471 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (_78901 : type1605) (h1 : _78901 = term125) : (term109 _123501 op f) = (term139 _123501 op _78901 f).
Proof. exact (MK_COMB (@lem6193470) (@lem6193469 _123501 op f _78901 h1)). Qed.
Lemma lem6193482 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : ((term140 _123501 op x) = x) = ((term140 _123501 op x) = x).
Proof. exact (eq_refl ((term140 _123501 op x) = x)). Qed.
Lemma lem6193483 {_123501 : Type'} (op : type1400 _123501) : (term141 _123501 op) = (term141 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6193482 _123501 op x)). Qed.
Lemma lem6193484 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193485 {_123501 : Type'} (op : type1400 _123501) : (term142 _123501 op) = (term142 _123501 op).
Proof. exact (MK_COMB (@lem6193484 _123501) (@lem6193483 _123501 op)). Qed.
Lemma lem6193506 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) (z : _123501) : ((term143 _123501 x op y z) = (term144 _123501 op x y z)) = ((term143 _123501 x op y z) = (term144 _123501 op x y z)).
Proof. exact (eq_refl ((term143 _123501 x op y z) = (term144 _123501 op x y z))). Qed.
Lemma lem6193507 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term145 _123501 op x y) = (term145 _123501 op x y).
Proof. exact (fun_ext (fun z : _123501 => @lem6193506 _123501 op x y z)). Qed.
Lemma lem6193508 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193509 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term146 _123501 op x y) = (term146 _123501 op x y).
Proof. exact (MK_COMB (@lem6193508 _123501) (@lem6193507 _123501 op x y)). Qed.
Lemma lem6193510 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term147 _123501 op x) = (term147 _123501 op x).
Proof. exact (fun_ext (fun y : _123501 => @lem6193509 _123501 op x y)). Qed.
Lemma lem6193511 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193512 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term148 _123501 op x) = (term148 _123501 op x).
Proof. exact (MK_COMB (@lem6193511 _123501) (@lem6193510 _123501 op x)). Qed.
Lemma lem6193513 {_123501 : Type'} (op : type1400 _123501) : (term149 _123501 op) = (term149 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6193512 _123501 op x)). Qed.
Lemma lem6193514 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193515 {_123501 : Type'} (op : type1400 _123501) : (term150 _123501 op) = (term150 _123501 op).
Proof. exact (MK_COMB (@lem6193514 _123501) (@lem6193513 _123501 op)). Qed.
Lemma lem6193516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6193517 {_123501 : Type'} (op : type1400 _123501) : (term151 _123501 op) = (term151 _123501 op).
Proof. exact (MK_COMB (@lem6193516) (@lem6193515 _123501 op)). Qed.
Lemma lem6193518 {_123501 : Type'} (op : type1400 _123501) : (term152 _123501 op) = (term152 _123501 op).
Proof. exact (MK_COMB (@lem6193517 _123501 op) (@lem6193485 _123501 op)). Qed.
Lemma lem6193531 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (x : _123501) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6193532 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term153 _123501 op x) = (term153 _123501 op x).
Proof. exact (fun_ext (fun y : _123501 => @lem6193531 _123501 op y x)). Qed.
Lemma lem6193533 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193534 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term154 _123501 op x) = (term154 _123501 op x).
Proof. exact (MK_COMB (@lem6193533 _123501) (@lem6193532 _123501 op x)). Qed.
Lemma lem6193535 {_123501 : Type'} (op : type1400 _123501) : (term155 _123501 op) = (term155 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6193534 _123501 op x)). Qed.
Lemma lem6193536 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193537 {_123501 : Type'} (op : type1400 _123501) : (term156 _123501 op) = (term156 _123501 op).
Proof. exact (MK_COMB (@lem6193536 _123501) (@lem6193535 _123501 op)). Qed.
Lemma lem6193538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6193539 {_123501 : Type'} (op : type1400 _123501) : (term157 _123501 op) = (term157 _123501 op).
Proof. exact (MK_COMB (@lem6193538) (@lem6193537 _123501 op)). Qed.
Lemma lem6193540 {_123501 : Type'} (op : type1400 _123501) : (term1 _123501 op) = (term1 _123501 op).
Proof. exact (MK_COMB (@lem6193539 _123501 op) (@lem6193518 _123501 op)). Qed.
Lemma lem6193541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6193542 {_123501 : Type'} (op : type1400 _123501) : (term81 _123501 op) = (term81 _123501 op).
Proof. exact (MK_COMB (@lem6193541) (@lem6193540 _123501 op)). Qed.
Lemma lem6193543 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (_78901 : type1605) (h1 : _78901 = term125) : (term110 _123501 op f) = (term158 _123501 op _78901 f).
Proof. exact (MK_COMB (@lem6193542 _123501 op) (@lem6193471 _123501 op f _78901 h1)). Qed.
Lemma lem6193544 {_123501 : Type'} (f : nat -> _123501) (_78901 : type1605) (h1 : _78901 = term125) : (term111 _123501 f) = (term159 _123501 _78901 f).
Proof. exact (fun_ext (fun op : type1400 _123501 => @lem6193543 _123501 op f _78901 h1)). Qed.
Lemma lem6193545 {_123501 : Type'} : (@all (_123501 -> _123501 -> _123501)) = (@all (_123501 -> _123501 -> _123501)).
Proof. exact (eq_refl (@all (_123501 -> _123501 -> _123501))). Qed.
Lemma lem6193546 {_123501 : Type'} (f : nat -> _123501) (_78901 : type1605) (h1 : _78901 = term125) : (term112 _123501 f) = (term160 _123501 _78901 f).
Proof. exact (MK_COMB (@lem6193545 _123501) (@lem6193544 _123501 f _78901 h1)). Qed.
Lemma lem6193547 {_123501 : Type'} (_78901 : type1605) (h1 : _78901 = term125) : (term122 _123501) = (term161 _123501 _78901).
Proof. exact (fun_ext (fun f : nat -> _123501 => @lem6193546 _123501 f _78901 h1)). Qed.
Lemma lem6193548 {_123501 : Type'} : (@all (nat -> _123501)) = (@all (nat -> _123501)).
Proof. exact (eq_refl (@all (nat -> _123501))). Qed.
Lemma lem6193549 {_123501 : Type'} (_78901 : type1605) (h1 : _78901 = term125) : (term124 _123501) = (term162 _123501 _78901).
Proof. exact (MK_COMB (@lem6193548 _123501) (@lem6193547 _123501 _78901 h1)). Qed.
Lemma lem6193550 {_123501 : Type'} (_78901 : type1605) : term163 _123501 _78901.
Proof. exact (fun h0 : _78901 = term125 => @lem6193549 _123501 _78901 h0). Qed.
Lemma lem6193551 {_123501 : Type'} : term164 _123501.
Proof. exact (fun _78901 : type1605 => @lem6193550 _123501 _78901). Qed.
Lemma lem6193553 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term165 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem6193554 (P : Prop) (c : type1605) (Q : type959) : term166 P c Q.
Proof. exact (@lem6193553 type1605 P c Q). Qed.
Lemma lem6193555 {_123501 : Type'} : term167 _123501.
Proof. exact (@lem6193554 (term124 _123501) term125 (term168 _123501)). Qed.
Lemma lem6193556 {_123501 : Type'} (_78901 : type1605) : (term169 _123501 _78901) = (term162 _123501 _78901).
Proof. exact (eq_refl (term169 _123501 _78901)). Qed.
Lemma lem6193557 {_123501 : Type'} : (term170 _123501) = (term170 _123501).
Proof. exact (eq_refl (term170 _123501)). Qed.
Lemma lem6193558 {_123501 : Type'} (_78901 : type1605) : ((term124 _123501) = (term169 _123501 _78901)) = ((term124 _123501) = (term162 _123501 _78901)).
Proof. exact (MK_COMB (@lem6193557 _123501) (@lem6193556 _123501 _78901)). Qed.
Lemma lem6193559 (_78901 : type1605) : (term171 _78901) = (term171 _78901).
Proof. exact (eq_refl (term171 _78901)). Qed.
Lemma lem6193560 {_123501 : Type'} (_78901 : type1605) : (term172 _123501 _78901) = (term163 _123501 _78901).
Proof. exact (MK_COMB (@lem6193559 _78901) (@lem6193558 _123501 _78901)). Qed.
Lemma lem6193561 {_123501 : Type'} : (term173 _123501) = (term174 _123501).
Proof. exact (fun_ext (fun _78901 : type1605 => @lem6193560 _123501 _78901)). Qed.
Lemma lem6193562 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem6193563 {_123501 : Type'} : (term175 _123501) = (term164 _123501).
Proof. exact (MK_COMB (@lem6193562) (@lem6193561 _123501)). Qed.
Lemma lem6193564 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6193565 {_123501 : Type'} : (term176 _123501) = (term177 _123501).
Proof. exact (MK_COMB (@lem6193564) (@lem6193563 _123501)). Qed.
Lemma lem6193566 {_123501 : Type'} (_78901 : type1605) : (term169 _123501 _78901) = (term162 _123501 _78901).
Proof. exact (eq_refl (term169 _123501 _78901)). Qed.
Lemma lem6193567 (_78901 : type1605) : (term171 _78901) = (term171 _78901).
Proof. exact (eq_refl (term171 _78901)). Qed.
Lemma lem6193568 {_123501 : Type'} (_78901 : type1605) : (term178 _123501 _78901) = (term179 _123501 _78901).
Proof. exact (MK_COMB (@lem6193567 _78901) (@lem6193566 _123501 _78901)). Qed.
Lemma lem6193569 {_123501 : Type'} : (term180 _123501) = (term181 _123501).
Proof. exact (fun_ext (fun _78901 : type1605 => @lem6193568 _123501 _78901)). Qed.
Lemma lem6193570 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem6193571 {_123501 : Type'} : (term182 _123501) = (term183 _123501).
Proof. exact (MK_COMB (@lem6193570) (@lem6193569 _123501)). Qed.
Lemma lem6193572 {_123501 : Type'} : (term170 _123501) = (term170 _123501).
Proof. exact (eq_refl (term170 _123501)). Qed.
Lemma lem6193573 {_123501 : Type'} : ((term124 _123501) = (term182 _123501)) = ((term124 _123501) = (term183 _123501)).
Proof. exact (MK_COMB (@lem6193572 _123501) (@lem6193571 _123501)). Qed.
Lemma lem6193574 {_123501 : Type'} : (term167 _123501) = (term184 _123501).
Proof. exact (MK_COMB (@lem6193565 _123501) (@lem6193573 _123501)). Qed.
Lemma lem6193575 {_123501 : Type'} : term184 _123501.
Proof. exact (EQ_MP (@lem6193574 _123501) (@lem6193555 _123501)). Qed.
Lemma lem6193576 {_123501 : Type'} : (term124 _123501) = (term183 _123501).
Proof. exact (@lem6193575 _123501 (@lem6193551 _123501)). Qed.
Lemma lem6193578 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term185 _3571 _3575 t)) = (term186 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6193579 (s : type1605) (t : type1605) : (s = (term187 t)) = (term188 s t).
Proof. exact (@lem6193578 (nat -> Prop) nat s t). Qed.
Lemma lem6193580 (_78901 : type1605) : (_78901 = term189) = (term190 _78901).
Proof. exact (@lem6193579 _78901 term125). Qed.
Lemma lem6193581 (k : nat) : (term126 k) = (term96 k).
Proof. exact (eq_refl (term126 k)). Qed.
Lemma lem6193582 : term189 = term125.
Proof. exact (fun_ext (fun k : nat => @lem6193581 k)). Qed.
Lemma lem6193583 (_78901 : type1605) : (@eq (nat -> nat -> Prop) _78901) = (@eq (nat -> nat -> Prop) _78901).
Proof. exact (eq_refl (@eq (nat -> nat -> Prop) _78901)). Qed.
Lemma lem6193584 (_78901 : type1605) : (_78901 = term189) = (_78901 = term125).
Proof. exact (MK_COMB (@lem6193583 _78901) (@lem6193582)). Qed.
Lemma lem6193585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6193586 (_78901 : type1605) : (term191 _78901) = (term192 _78901).
Proof. exact (MK_COMB (@lem6193585) (@lem6193584 _78901)). Qed.
Lemma lem6193587 (k : nat) : (term126 k) = (term96 k).
Proof. exact (eq_refl (term126 k)). Qed.
Lemma lem6193588 (_78901 : type1605) (k : nat) : (term127 _78901 k) = (term127 _78901 k).
Proof. exact (eq_refl (term127 _78901 k)). Qed.
Lemma lem6193589 (_78901 : type1605) (k : nat) : ((_78901 k) = (term126 k)) = ((_78901 k) = (term96 k)).
Proof. exact (MK_COMB (@lem6193588 _78901 k) (@lem6193587 k)). Qed.
Lemma lem6193590 (_78901 : type1605) : (term193 _78901) = (term194 _78901).
Proof. exact (fun_ext (fun k : nat => @lem6193589 _78901 k)). Qed.
Lemma lem6193591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193592 (_78901 : type1605) : (term190 _78901) = (term195 _78901).
Proof. exact (MK_COMB (@lem6193591) (@lem6193590 _78901)). Qed.
Lemma lem6193593 (_78901 : type1605) : ((_78901 = term189) = (term190 _78901)) = ((_78901 = term125) = (term195 _78901)).
Proof. exact (MK_COMB (@lem6193586 _78901) (@lem6193592 _78901)). Qed.
Lemma lem6193594 (_78901 : type1605) : (_78901 = term125) = (term195 _78901).
Proof. exact (EQ_MP (@lem6193593 _78901) (@lem6193580 _78901)). Qed.
Lemma lem6193596 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term185 _3571 _3575 t)) = (term186 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6193597 (s : nat -> Prop) (t : nat -> Prop) : (s = (term196 t)) = (term197 s t).
Proof. exact (@lem6193596 Prop nat s t). Qed.
Lemma lem6193598 (_78901 : type1605) (k : nat) : ((_78901 k) = (term198 k)) = (term199 _78901 k).
Proof. exact (@lem6193597 (_78901 k) (term96 k)). Qed.
Lemma lem6193599 (GEN_PVAR_181 : nat) (k : nat) : (term200 k GEN_PVAR_181) = (term94 GEN_PVAR_181 k).
Proof. exact (eq_refl (term200 k GEN_PVAR_181)). Qed.
Lemma lem6193600 (k : nat) : (term198 k) = (term96 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6193599 GEN_PVAR_181 k)). Qed.
Lemma lem6193601 (_78901 : type1605) (k : nat) : (term127 _78901 k) = (term127 _78901 k).
Proof. exact (eq_refl (term127 _78901 k)). Qed.
Lemma lem6193602 (_78901 : type1605) (k : nat) : ((_78901 k) = (term198 k)) = ((_78901 k) = (term96 k)).
Proof. exact (MK_COMB (@lem6193601 _78901 k) (@lem6193600 k)). Qed.
Lemma lem6193603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6193604 (_78901 : type1605) (k : nat) : (term201 _78901 k) = (term202 _78901 k).
Proof. exact (MK_COMB (@lem6193603) (@lem6193602 _78901 k)). Qed.
Lemma lem6193605 (GEN_PVAR_181 : nat) (k : nat) : (term200 k GEN_PVAR_181) = (term94 GEN_PVAR_181 k).
Proof. exact (eq_refl (term200 k GEN_PVAR_181)). Qed.
Lemma lem6193606 (_78901 : type1605) (k : nat) (GEN_PVAR_181 : nat) : (term203 _78901 k GEN_PVAR_181) = (term203 _78901 k GEN_PVAR_181).
Proof. exact (eq_refl (term203 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6193607 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : ((_78901 k GEN_PVAR_181) = (term200 k GEN_PVAR_181)) = ((_78901 k GEN_PVAR_181) = (term94 GEN_PVAR_181 k)).
Proof. exact (MK_COMB (@lem6193606 _78901 k GEN_PVAR_181) (@lem6193605 GEN_PVAR_181 k)). Qed.
Lemma lem6193608 (_78901 : type1605) (k : nat) : (term204 _78901 k) = (term205 _78901 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6193607 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193609 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193610 (_78901 : type1605) (k : nat) : (term199 _78901 k) = (term206 _78901 k).
Proof. exact (MK_COMB (@lem6193609) (@lem6193608 _78901 k)). Qed.
Lemma lem6193611 (_78901 : type1605) (k : nat) : (((_78901 k) = (term198 k)) = (term199 _78901 k)) = (((_78901 k) = (term96 k)) = (term206 _78901 k)).
Proof. exact (MK_COMB (@lem6193604 _78901 k) (@lem6193610 _78901 k)). Qed.
Lemma lem6193612 (_78901 : type1605) (k : nat) : ((_78901 k) = (term96 k)) = (term206 _78901 k).
Proof. exact (EQ_MP (@lem6193611 _78901 k) (@lem6193598 _78901 k)). Qed.
Lemma lem6193613 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : ((_78901 k GEN_PVAR_181) = (term94 GEN_PVAR_181 k)) = ((_78901 k GEN_PVAR_181) = (term94 GEN_PVAR_181 k)).
Proof. exact (eq_refl ((_78901 k GEN_PVAR_181) = (term94 GEN_PVAR_181 k))). Qed.
Lemma lem6193614 (_78901 : type1605) (k : nat) : (term205 _78901 k) = (term205 _78901 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6193613 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193615 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193616 (_78901 : type1605) (k : nat) : (term206 _78901 k) = (term206 _78901 k).
Proof. exact (MK_COMB (@lem6193615) (@lem6193614 _78901 k)). Qed.
Lemma lem6193617 (_78901 : type1605) (k : nat) : ((_78901 k) = (term96 k)) = (term206 _78901 k).
Proof. exact (TRANS (@lem6193612 _78901 k) (@lem6193616 _78901 k)). Qed.
Lemma lem6193618 (_78901 : type1605) : (term194 _78901) = (term207 _78901).
Proof. exact (fun_ext (fun k : nat => @lem6193617 _78901 k)). Qed.
Lemma lem6193619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193620 (_78901 : type1605) : (term195 _78901) = (term208 _78901).
Proof. exact (MK_COMB (@lem6193619) (@lem6193618 _78901)). Qed.
Lemma lem6193621 (_78901 : type1605) : (_78901 = term125) = (term208 _78901).
Proof. exact (TRANS (@lem6193594 _78901) (@lem6193620 _78901)). Qed.
Lemma lem6193622 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6193623 (_78901 : type1605) : (term171 _78901) = (term209 _78901).
Proof. exact (MK_COMB (@lem6193622) (@lem6193621 _78901)). Qed.
Lemma lem6193624 {_123501 : Type'} (_78901 : type1605) : (term162 _123501 _78901) = (term162 _123501 _78901).
Proof. exact (eq_refl (term162 _123501 _78901)). Qed.
Lemma lem6193625 {_123501 : Type'} (_78901 : type1605) : (term179 _123501 _78901) = (term210 _123501 _78901).
Proof. exact (MK_COMB (@lem6193623 _78901) (@lem6193624 _123501 _78901)). Qed.
Lemma lem6193626 {_123501 : Type'} : (term181 _123501) = (term211 _123501).
Proof. exact (fun_ext (fun _78901 : type1605 => @lem6193625 _123501 _78901)). Qed.
Lemma lem6193627 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem6193628 {_123501 : Type'} : (term183 _123501) = (term212 _123501).
Proof. exact (MK_COMB (@lem6193627) (@lem6193626 _123501)). Qed.
Lemma lem6193629 {_123501 : Type'} : (term170 _123501) = (term170 _123501).
Proof. exact (eq_refl (term170 _123501)). Qed.
Lemma lem6193630 {_123501 : Type'} : ((term124 _123501) = (term183 _123501)) = ((term124 _123501) = (term212 _123501)).
Proof. exact (MK_COMB (@lem6193629 _123501) (@lem6193628 _123501)). Qed.
Lemma lem6193633 {_123501 : Type'} : (term124 _123501) = (term212 _123501).
Proof. exact (EQ_MP (@lem6193630 _123501) (@lem6193576 _123501)). Qed.
Lemma lem6193634 {_123501 : Type'} : (term123 _123501) = (term212 _123501).
Proof. exact (TRANS (@lem6193425 _123501) (@lem6193633 _123501)). Qed.
Lemma lem6193635 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : ((term136 _123501 op _78901 k f) = (term134 _123501 op _78901 f k)) = ((term136 _123501 op _78901 k f) = (term134 _123501 op _78901 f k)).
Proof. exact (eq_refl ((term136 _123501 op _78901 k f) = (term134 _123501 op _78901 f k))). Qed.
Lemma lem6193636 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) : (term138 _123501 op _78901 f) = (term138 _123501 op _78901 f).
Proof. exact (fun_ext (fun k : nat => @lem6193635 _123501 op _78901 f k)). Qed.
Lemma lem6193637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193638 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) : (term139 _123501 op _78901 f) = (term139 _123501 op _78901 f).
Proof. exact (MK_COMB (@lem6193637) (@lem6193636 _123501 op _78901 f)). Qed.
Lemma lem6193639 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : ((term140 _123501 op x) = x) = ((term140 _123501 op x) = x).
Proof. exact (eq_refl ((term140 _123501 op x) = x)). Qed.
Lemma lem6193640 {_123501 : Type'} (op : type1400 _123501) : (term141 _123501 op) = (term141 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6193639 _123501 op x)). Qed.
Lemma lem6193641 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193642 {_123501 : Type'} (op : type1400 _123501) : (term142 _123501 op) = (term142 _123501 op).
Proof. exact (MK_COMB (@lem6193641 _123501) (@lem6193640 _123501 op)). Qed.
Lemma lem6193643 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) (z : _123501) : ((term143 _123501 x op y z) = (term144 _123501 op x y z)) = ((term143 _123501 x op y z) = (term144 _123501 op x y z)).
Proof. exact (eq_refl ((term143 _123501 x op y z) = (term144 _123501 op x y z))). Qed.
Lemma lem6193644 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term145 _123501 op x y) = (term145 _123501 op x y).
Proof. exact (fun_ext (fun z : _123501 => @lem6193643 _123501 op x y z)). Qed.
Lemma lem6193645 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193646 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term146 _123501 op x y) = (term146 _123501 op x y).
Proof. exact (MK_COMB (@lem6193645 _123501) (@lem6193644 _123501 op x y)). Qed.
Lemma lem6193647 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term147 _123501 op x) = (term147 _123501 op x).
Proof. exact (fun_ext (fun y : _123501 => @lem6193646 _123501 op x y)). Qed.
Lemma lem6193648 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193649 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term148 _123501 op x) = (term148 _123501 op x).
Proof. exact (MK_COMB (@lem6193648 _123501) (@lem6193647 _123501 op x)). Qed.
Lemma lem6193650 {_123501 : Type'} (op : type1400 _123501) : (term149 _123501 op) = (term149 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6193649 _123501 op x)). Qed.
Lemma lem6193651 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193652 {_123501 : Type'} (op : type1400 _123501) : (term150 _123501 op) = (term150 _123501 op).
Proof. exact (MK_COMB (@lem6193651 _123501) (@lem6193650 _123501 op)). Qed.
Lemma lem6193653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6193654 {_123501 : Type'} (op : type1400 _123501) : (term151 _123501 op) = (term151 _123501 op).
Proof. exact (MK_COMB (@lem6193653) (@lem6193652 _123501 op)). Qed.
Lemma lem6193655 {_123501 : Type'} (op : type1400 _123501) : (term152 _123501 op) = (term152 _123501 op).
Proof. exact (MK_COMB (@lem6193654 _123501 op) (@lem6193642 _123501 op)). Qed.
Lemma lem6193656 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (x : _123501) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6193657 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term153 _123501 op x) = (term153 _123501 op x).
Proof. exact (fun_ext (fun y : _123501 => @lem6193656 _123501 op y x)). Qed.
Lemma lem6193658 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193659 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term154 _123501 op x) = (term154 _123501 op x).
Proof. exact (MK_COMB (@lem6193658 _123501) (@lem6193657 _123501 op x)). Qed.
Lemma lem6193660 {_123501 : Type'} (op : type1400 _123501) : (term155 _123501 op) = (term155 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6193659 _123501 op x)). Qed.
Lemma lem6193661 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6193662 {_123501 : Type'} (op : type1400 _123501) : (term156 _123501 op) = (term156 _123501 op).
Proof. exact (MK_COMB (@lem6193661 _123501) (@lem6193660 _123501 op)). Qed.
Lemma lem6193663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6193664 {_123501 : Type'} (op : type1400 _123501) : (term157 _123501 op) = (term157 _123501 op).
Proof. exact (MK_COMB (@lem6193663) (@lem6193662 _123501 op)). Qed.
Lemma lem6193665 {_123501 : Type'} (op : type1400 _123501) : (term1 _123501 op) = (term1 _123501 op).
Proof. exact (MK_COMB (@lem6193664 _123501 op) (@lem6193655 _123501 op)). Qed.
Lemma lem6193666 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6193667 {_123501 : Type'} (op : type1400 _123501) : (term81 _123501 op) = (term81 _123501 op).
Proof. exact (MK_COMB (@lem6193666) (@lem6193665 _123501 op)). Qed.
Lemma lem6193668 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) : (term158 _123501 op _78901 f) = (term158 _123501 op _78901 f).
Proof. exact (MK_COMB (@lem6193667 _123501 op) (@lem6193638 _123501 op _78901 f)). Qed.
Lemma lem6193669 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) : (term159 _123501 _78901 f) = (term159 _123501 _78901 f).
Proof. exact (fun_ext (fun op : type1400 _123501 => @lem6193668 _123501 op _78901 f)). Qed.
Lemma lem6193670 {_123501 : Type'} : (@all (_123501 -> _123501 -> _123501)) = (@all (_123501 -> _123501 -> _123501)).
Proof. exact (eq_refl (@all (_123501 -> _123501 -> _123501))). Qed.
Lemma lem6193671 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) : (term160 _123501 _78901 f) = (term160 _123501 _78901 f).
Proof. exact (MK_COMB (@lem6193670 _123501) (@lem6193669 _123501 _78901 f)). Qed.
Lemma lem6193672 {_123501 : Type'} (_78901 : type1605) : (term161 _123501 _78901) = (term161 _123501 _78901).
Proof. exact (fun_ext (fun f : nat -> _123501 => @lem6193671 _123501 _78901 f)). Qed.
Lemma lem6193673 {_123501 : Type'} : (@all (nat -> _123501)) = (@all (nat -> _123501)).
Proof. exact (eq_refl (@all (nat -> _123501))). Qed.
Lemma lem6193674 {_123501 : Type'} (_78901 : type1605) : (term162 _123501 _78901) = (term162 _123501 _78901).
Proof. exact (MK_COMB (@lem6193673 _123501) (@lem6193672 _123501 _78901)). Qed.
Lemma lem6193675 (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term90 GEN_PVAR_181 k i) = (term90 GEN_PVAR_181 k i).
Proof. exact (eq_refl (term90 GEN_PVAR_181 k i)). Qed.
Lemma lem6193676 (GEN_PVAR_181 : nat) (k : nat) : (term92 GEN_PVAR_181 k) = (term92 GEN_PVAR_181 k).
Proof. exact (fun_ext (fun i : nat => @lem6193675 GEN_PVAR_181 k i)). Qed.
Lemma lem6193677 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6193678 (GEN_PVAR_181 : nat) (k : nat) : (term94 GEN_PVAR_181 k) = (term94 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6193677) (@lem6193676 GEN_PVAR_181 k)). Qed.
Lemma lem6193681 (_78901 : type1605) (k : nat) (GEN_PVAR_181 : nat) : (term203 _78901 k GEN_PVAR_181) = (term203 _78901 k GEN_PVAR_181).
Proof. exact (eq_refl (term203 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6193682 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : ((_78901 k GEN_PVAR_181) = (term94 GEN_PVAR_181 k)) = ((_78901 k GEN_PVAR_181) = (term94 GEN_PVAR_181 k)).
Proof. exact (MK_COMB (@lem6193681 _78901 k GEN_PVAR_181) (@lem6193678 GEN_PVAR_181 k)). Qed.
Lemma lem6193683 (_78901 : type1605) (k : nat) : (term205 _78901 k) = (term205 _78901 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6193682 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193684 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193685 (_78901 : type1605) (k : nat) : (term206 _78901 k) = (term206 _78901 k).
Proof. exact (MK_COMB (@lem6193684) (@lem6193683 _78901 k)). Qed.
Lemma lem6193686 (_78901 : type1605) : (term207 _78901) = (term207 _78901).
Proof. exact (fun_ext (fun k : nat => @lem6193685 _78901 k)). Qed.
Lemma lem6193687 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193688 (_78901 : type1605) : (term208 _78901) = (term208 _78901).
Proof. exact (MK_COMB (@lem6193687) (@lem6193686 _78901)). Qed.
Lemma lem6193689 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6193690 (_78901 : type1605) : (term209 _78901) = (term209 _78901).
Proof. exact (MK_COMB (@lem6193689) (@lem6193688 _78901)). Qed.
Lemma lem6193691 {_123501 : Type'} (_78901 : type1605) : (term210 _123501 _78901) = (term210 _123501 _78901).
Proof. exact (MK_COMB (@lem6193690 _78901) (@lem6193674 _123501 _78901)). Qed.
Lemma lem6193692 {_123501 : Type'} : (term211 _123501) = (term211 _123501).
Proof. exact (fun_ext (fun _78901 : type1605 => @lem6193691 _123501 _78901)). Qed.
Lemma lem6193693 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem6193694 {_123501 : Type'} : (term212 _123501) = (term212 _123501).
Proof. exact (MK_COMB (@lem6193693) (@lem6193692 _123501)). Qed.
Lemma lem6193783 {_123501 : Type'} : (term123 _123501) = (term212 _123501).
Proof. exact (TRANS (@lem6193634 _123501) (@lem6193694 _123501)). Qed.
Lemma lem6193784 {_123501 : Type'} : (term212 _123501) = (term123 _123501).
Proof. exact (SYM (@lem6193783 _123501)). Qed.
Lemma lem6193785 (_78901 : type1605) (h1 : term208 _78901) : term208 _78901.
Proof. exact (h1). Qed.
Lemma lem6193786 {_123501 : Type'} (op : type1400 _123501) (h1 : term1 _123501 op) : term1 _123501 op.
Proof. exact (h1). Qed.
Lemma lem6193788 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6193789 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : ((term136 _123501 op _78901 k f) = (term134 _123501 op _78901 f k)) = (term213 _123501 op _78901 f k).
Proof. exact (@lem6193788 ((term136 _123501 op _78901 k f) = (term134 _123501 op _78901 f k))). Qed.
Lemma lem6193790 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : (term213 _123501 op _78901 f k) = ((term136 _123501 op _78901 k f) = (term134 _123501 op _78901 f k)).
Proof. exact (SYM (@lem6193789 _123501 op _78901 f k)). Qed.
Lemma lem6193791 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) (h1 : term214 _123501 op _78901 f k) : term214 _123501 op _78901 f k.
Proof. exact (h1). Qed.
Lemma lem6193795 (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term90 GEN_PVAR_181 k i) = (term90 GEN_PVAR_181 k i).
Proof. exact (eq_refl (term90 GEN_PVAR_181 k i)). Qed.
Lemma lem6193796 (P : nat -> Prop) : (term215 P) = (term216 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem6193797 (GEN_PVAR_181 : nat) (k : nat) : (term217 GEN_PVAR_181 k) = (term218 GEN_PVAR_181 k).
Proof. exact (@lem6193796 (term92 GEN_PVAR_181 k)). Qed.
Lemma lem6193798 (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term219 GEN_PVAR_181 k i) = (term90 GEN_PVAR_181 k i).
Proof. exact (eq_refl (term219 GEN_PVAR_181 k i)). Qed.
Lemma lem6193799 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6193801 (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term220 GEN_PVAR_181 k i) = (term221 GEN_PVAR_181 k i).
Proof. exact (MK_COMB (@lem6193799) (@lem6193798 GEN_PVAR_181 k i)). Qed.
Lemma lem6193802 (GEN_PVAR_181 : nat) (k : nat) : (term222 GEN_PVAR_181 k) = (term223 GEN_PVAR_181 k).
Proof. exact (fun_ext (fun i : nat => @lem6193801 GEN_PVAR_181 k i)). Qed.
Lemma lem6193803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193804 (GEN_PVAR_181 : nat) (k : nat) : (term218 GEN_PVAR_181 k) = (term224 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6193803) (@lem6193802 GEN_PVAR_181 k)). Qed.
Lemma lem6193805 (GEN_PVAR_181 : nat) (k : nat) : (term217 GEN_PVAR_181 k) = (term224 GEN_PVAR_181 k).
Proof. exact (TRANS (@lem6193797 GEN_PVAR_181 k) (@lem6193804 GEN_PVAR_181 k)). Qed.
Lemma lem6193806 (GEN_PVAR_181 : nat) (k : nat) : (term92 GEN_PVAR_181 k) = (term92 GEN_PVAR_181 k).
Proof. exact (fun_ext (fun i : nat => @lem6193795 GEN_PVAR_181 k i)). Qed.
Lemma lem6193807 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6193808 (GEN_PVAR_181 : nat) (k : nat) : (term94 GEN_PVAR_181 k) = (term94 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6193807) (@lem6193806 GEN_PVAR_181 k)). Qed.
Lemma lem6193810 (_78901 : type1605) (k : nat) (GEN_PVAR_181 : nat) : (term225 _78901 k GEN_PVAR_181) = (term225 _78901 k GEN_PVAR_181).
Proof. exact (eq_refl (term225 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6193811 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term226 _78901 GEN_PVAR_181 k) = (term226 _78901 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6193810 _78901 k GEN_PVAR_181) (@lem6193808 GEN_PVAR_181 k)). Qed.
Lemma lem6193813 (_78901 : type1605) (k : nat) (GEN_PVAR_181 : nat) : (term227 _78901 k GEN_PVAR_181) = (term227 _78901 k GEN_PVAR_181).
Proof. exact (eq_refl (term227 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6193814 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term228 _78901 GEN_PVAR_181 k) = (term229 _78901 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6193813 _78901 k GEN_PVAR_181) (@lem6193805 GEN_PVAR_181 k)). Qed.
Lemma lem6193815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6193816 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term230 _78901 GEN_PVAR_181 k) = (term231 _78901 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6193815) (@lem6193814 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193817 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term232 _78901 GEN_PVAR_181 k) = (term233 _78901 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6193816 _78901 GEN_PVAR_181 k) (@lem6193811 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193818 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : ((_78901 k GEN_PVAR_181) = (term94 GEN_PVAR_181 k)) = (term232 _78901 GEN_PVAR_181 k).
Proof. exact (@lem17784 (_78901 k GEN_PVAR_181) (term94 GEN_PVAR_181 k)). Qed.
Lemma lem6193819 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : ((_78901 k GEN_PVAR_181) = (term94 GEN_PVAR_181 k)) = (term233 _78901 GEN_PVAR_181 k).
Proof. exact (TRANS (@lem6193818 _78901 GEN_PVAR_181 k) (@lem6193817 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193820 (_78901 : type1605) (k : nat) : (term205 _78901 k) = (term234 _78901 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6193819 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193821 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193822 (_78901 : type1605) (k : nat) : (term206 _78901 k) = (term235 _78901 k).
Proof. exact (MK_COMB (@lem6193821) (@lem6193820 _78901 k)). Qed.
Lemma lem6193823 (_78901 : type1605) : (term207 _78901) = (term236 _78901).
Proof. exact (fun_ext (fun k : nat => @lem6193822 _78901 k)). Qed.
Lemma lem6193824 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193825 (_78901 : type1605) : (term208 _78901) = (term237 _78901).
Proof. exact (MK_COMB (@lem6193824) (@lem6193823 _78901)). Qed.
Lemma lem6193831 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term238 A P Q) = (term239 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6193832 (P : nat -> Prop) (Q : nat -> Prop) : (term240 P Q) = (term241 P Q).
Proof. exact (@lem6193831 nat P Q). Qed.
Lemma lem6193833 (_78901 : type1605) (k : nat) : (term242 _78901 k) = (term243 _78901 k).
Proof. exact (@lem6193832 (term244 _78901 k) (term245 _78901 k)). Qed.
Lemma lem6193834 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term246 _78901 k GEN_PVAR_181) = (term229 _78901 GEN_PVAR_181 k).
Proof. exact (eq_refl (term246 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6193835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6193836 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term247 _78901 k GEN_PVAR_181) = (term231 _78901 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6193835) (@lem6193834 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193837 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term248 _78901 k GEN_PVAR_181) = (term226 _78901 GEN_PVAR_181 k).
Proof. exact (eq_refl (term248 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6193838 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term249 _78901 k GEN_PVAR_181) = (term233 _78901 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6193836 _78901 GEN_PVAR_181 k) (@lem6193837 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193839 (_78901 : type1605) (k : nat) : (term250 _78901 k) = (term234 _78901 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6193838 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193840 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193841 (_78901 : type1605) (k : nat) : (term242 _78901 k) = (term235 _78901 k).
Proof. exact (MK_COMB (@lem6193840) (@lem6193839 _78901 k)). Qed.
Lemma lem6193842 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6193843 (_78901 : type1605) (k : nat) : (term251 _78901 k) = (term252 _78901 k).
Proof. exact (MK_COMB (@lem6193842) (@lem6193841 _78901 k)). Qed.
Lemma lem6193844 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term246 _78901 k GEN_PVAR_181) = (term229 _78901 GEN_PVAR_181 k).
Proof. exact (eq_refl (term246 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6193845 (_78901 : type1605) (k : nat) : (term253 _78901 k) = (term244 _78901 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6193844 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193846 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193847 (_78901 : type1605) (k : nat) : (term254 _78901 k) = (term255 _78901 k).
Proof. exact (MK_COMB (@lem6193846) (@lem6193845 _78901 k)). Qed.
Lemma lem6193848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6193849 (_78901 : type1605) (k : nat) : (term256 _78901 k) = (term257 _78901 k).
Proof. exact (MK_COMB (@lem6193848) (@lem6193847 _78901 k)). Qed.
Lemma lem6193850 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term248 _78901 k GEN_PVAR_181) = (term226 _78901 GEN_PVAR_181 k).
Proof. exact (eq_refl (term248 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6193851 (_78901 : type1605) (k : nat) : (term258 _78901 k) = (term245 _78901 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6193850 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6193852 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193853 (_78901 : type1605) (k : nat) : (term259 _78901 k) = (term260 _78901 k).
Proof. exact (MK_COMB (@lem6193852) (@lem6193851 _78901 k)). Qed.
Lemma lem6193854 (_78901 : type1605) (k : nat) : (term243 _78901 k) = (term261 _78901 k).
Proof. exact (MK_COMB (@lem6193849 _78901 k) (@lem6193853 _78901 k)). Qed.
Lemma lem6193855 (_78901 : type1605) (k : nat) : ((term242 _78901 k) = (term243 _78901 k)) = ((term235 _78901 k) = (term261 _78901 k)).
Proof. exact (MK_COMB (@lem6193843 _78901 k) (@lem6193854 _78901 k)). Qed.
Lemma lem6193856 (_78901 : type1605) (k : nat) : (term235 _78901 k) = (term261 _78901 k).
Proof. exact (EQ_MP (@lem6193855 _78901 k) (@lem6193833 _78901 k)). Qed.
Lemma lem6193961 (_78901 : type1605) : (term236 _78901) = (term262 _78901).
Proof. exact (fun_ext (fun k : nat => @lem6193856 _78901 k)). Qed.
Lemma lem6193962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193963 (_78901 : type1605) : (term237 _78901) = (term263 _78901).
Proof. exact (MK_COMB (@lem6193962) (@lem6193961 _78901)). Qed.
Lemma lem6193965 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term238 A P Q) = (term239 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6193966 (P : nat -> Prop) (Q : nat -> Prop) : (term240 P Q) = (term241 P Q).
Proof. exact (@lem6193965 nat P Q). Qed.
Lemma lem6193967 (_78901 : type1605) : (term264 _78901) = (term265 _78901).
Proof. exact (@lem6193966 (term266 _78901) (term267 _78901)). Qed.
Lemma lem6193968 (_78901 : type1605) (k : nat) : (term268 _78901 k) = (term255 _78901 k).
Proof. exact (eq_refl (term268 _78901 k)). Qed.
Lemma lem6193969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6193970 (_78901 : type1605) (k : nat) : (term269 _78901 k) = (term257 _78901 k).
Proof. exact (MK_COMB (@lem6193969) (@lem6193968 _78901 k)). Qed.
Lemma lem6193971 (_78901 : type1605) (k : nat) : (term270 _78901 k) = (term260 _78901 k).
Proof. exact (eq_refl (term270 _78901 k)). Qed.
Lemma lem6193972 (_78901 : type1605) (k : nat) : (term271 _78901 k) = (term261 _78901 k).
Proof. exact (MK_COMB (@lem6193970 _78901 k) (@lem6193971 _78901 k)). Qed.
Lemma lem6193973 (_78901 : type1605) : (term272 _78901) = (term262 _78901).
Proof. exact (fun_ext (fun k : nat => @lem6193972 _78901 k)). Qed.
Lemma lem6193974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193975 (_78901 : type1605) : (term264 _78901) = (term263 _78901).
Proof. exact (MK_COMB (@lem6193974) (@lem6193973 _78901)). Qed.
Lemma lem6193976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6193977 (_78901 : type1605) : (term273 _78901) = (term274 _78901).
Proof. exact (MK_COMB (@lem6193976) (@lem6193975 _78901)). Qed.
Lemma lem6193978 (_78901 : type1605) (k : nat) : (term268 _78901 k) = (term255 _78901 k).
Proof. exact (eq_refl (term268 _78901 k)). Qed.
Lemma lem6193979 (_78901 : type1605) : (term275 _78901) = (term266 _78901).
Proof. exact (fun_ext (fun k : nat => @lem6193978 _78901 k)). Qed.
Lemma lem6193980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193981 (_78901 : type1605) : (term276 _78901) = (term277 _78901).
Proof. exact (MK_COMB (@lem6193980) (@lem6193979 _78901)). Qed.
Lemma lem6193982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6193983 (_78901 : type1605) : (term278 _78901) = (term279 _78901).
Proof. exact (MK_COMB (@lem6193982) (@lem6193981 _78901)). Qed.
Lemma lem6193984 (_78901 : type1605) (k : nat) : (term270 _78901 k) = (term260 _78901 k).
Proof. exact (eq_refl (term270 _78901 k)). Qed.
Lemma lem6193985 (_78901 : type1605) : (term280 _78901) = (term267 _78901).
Proof. exact (fun_ext (fun k : nat => @lem6193984 _78901 k)). Qed.
Lemma lem6193986 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6193987 (_78901 : type1605) : (term281 _78901) = (term282 _78901).
Proof. exact (MK_COMB (@lem6193986) (@lem6193985 _78901)). Qed.
Lemma lem6193988 (_78901 : type1605) : (term265 _78901) = (term283 _78901).
Proof. exact (MK_COMB (@lem6193983 _78901) (@lem6193987 _78901)). Qed.
Lemma lem6193989 (_78901 : type1605) : ((term264 _78901) = (term265 _78901)) = ((term263 _78901) = (term283 _78901)).
Proof. exact (MK_COMB (@lem6193977 _78901) (@lem6193988 _78901)). Qed.
Lemma lem6193990 (_78901 : type1605) : (term263 _78901) = (term283 _78901).
Proof. exact (EQ_MP (@lem6193989 _78901) (@lem6193967 _78901)). Qed.
Lemma lem6194103 (_78901 : type1605) : (term237 _78901) = (term283 _78901).
Proof. exact (TRANS (@lem6193963 _78901) (@lem6193990 _78901)). Qed.
Lemma lem6194105 {A : Type'} (P : Prop) (Q : A -> Prop) : (term284 A P Q) = (term285 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6194106 (P : Prop) (Q : nat -> Prop) : (term286 P Q) = (term287 P Q).
Proof. exact (@lem6194105 nat P Q). Qed.
Lemma lem6194107 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term288 _78901 GEN_PVAR_181 k) = (term289 _78901 GEN_PVAR_181 k).
Proof. exact (@lem6194106 (term290 _78901 k GEN_PVAR_181) (term92 GEN_PVAR_181 k)). Qed.
Lemma lem6194108 (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term219 GEN_PVAR_181 k i) = (term90 GEN_PVAR_181 k i).
Proof. exact (eq_refl (term219 GEN_PVAR_181 k i)). Qed.
Lemma lem6194109 (GEN_PVAR_181 : nat) (k : nat) : (term291 GEN_PVAR_181 k) = (term92 GEN_PVAR_181 k).
Proof. exact (fun_ext (fun i : nat => @lem6194108 GEN_PVAR_181 k i)). Qed.
Lemma lem6194110 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6194111 (GEN_PVAR_181 : nat) (k : nat) : (term292 GEN_PVAR_181 k) = (term94 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6194110) (@lem6194109 GEN_PVAR_181 k)). Qed.
Lemma lem6194112 (_78901 : type1605) (k : nat) (GEN_PVAR_181 : nat) : (term225 _78901 k GEN_PVAR_181) = (term225 _78901 k GEN_PVAR_181).
Proof. exact (eq_refl (term225 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6194113 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term288 _78901 GEN_PVAR_181 k) = (term226 _78901 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6194112 _78901 k GEN_PVAR_181) (@lem6194111 GEN_PVAR_181 k)). Qed.
Lemma lem6194114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6194115 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term293 _78901 GEN_PVAR_181 k) = (term294 _78901 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6194114) (@lem6194113 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6194116 (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term219 GEN_PVAR_181 k i) = (term90 GEN_PVAR_181 k i).
Proof. exact (eq_refl (term219 GEN_PVAR_181 k i)). Qed.
Lemma lem6194117 (_78901 : type1605) (k : nat) (GEN_PVAR_181 : nat) : (term225 _78901 k GEN_PVAR_181) = (term225 _78901 k GEN_PVAR_181).
Proof. exact (eq_refl (term225 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6194118 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term295 _78901 GEN_PVAR_181 k i) = (term296 _78901 GEN_PVAR_181 k i).
Proof. exact (MK_COMB (@lem6194117 _78901 k GEN_PVAR_181) (@lem6194116 GEN_PVAR_181 k i)). Qed.
Lemma lem6194119 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term297 _78901 GEN_PVAR_181 k) = (term298 _78901 GEN_PVAR_181 k).
Proof. exact (fun_ext (fun i : nat => @lem6194118 _78901 GEN_PVAR_181 k i)). Qed.
Lemma lem6194120 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6194121 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term289 _78901 GEN_PVAR_181 k) = (term299 _78901 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6194120) (@lem6194119 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6194122 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : ((term288 _78901 GEN_PVAR_181 k) = (term289 _78901 GEN_PVAR_181 k)) = ((term226 _78901 GEN_PVAR_181 k) = (term299 _78901 GEN_PVAR_181 k)).
Proof. exact (MK_COMB (@lem6194115 _78901 GEN_PVAR_181 k) (@lem6194121 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6194123 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term226 _78901 GEN_PVAR_181 k) = (term299 _78901 GEN_PVAR_181 k).
Proof. exact (EQ_MP (@lem6194122 _78901 GEN_PVAR_181 k) (@lem6194107 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6194124 (_78901 : type1605) (k : nat) : (term245 _78901 k) = (term300 _78901 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6194123 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6194125 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6194126 (_78901 : type1605) (k : nat) : (term260 _78901 k) = (term301 _78901 k).
Proof. exact (MK_COMB (@lem6194125) (@lem6194124 _78901 k)). Qed.
Lemma lem6194128 {A B : Type'} (P : type1413 A B) : (term302 A B P) = (term303 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6194129 (P : type1605) : (term304 P) = (term305 P).
Proof. exact (@lem6194128 nat nat P). Qed.
Lemma lem6194130 (_78901 : type1605) (k : nat) : (term306 _78901 k) = (term307 _78901 k).
Proof. exact (@lem6194129 (term308 _78901 k)). Qed.
Lemma lem6194131 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term309 _78901 k GEN_PVAR_181) = (term298 _78901 GEN_PVAR_181 k).
Proof. exact (eq_refl (term309 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6194132 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6194133 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term310 _78901 k GEN_PVAR_181 i) = (term311 _78901 GEN_PVAR_181 k i).
Proof. exact (MK_COMB (@lem6194131 _78901 GEN_PVAR_181 k) (@lem6194132 i)). Qed.
Lemma lem6194134 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term311 _78901 GEN_PVAR_181 k i) = (term296 _78901 GEN_PVAR_181 k i).
Proof. exact (eq_refl (term311 _78901 GEN_PVAR_181 k i)). Qed.
Lemma lem6194135 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) (i : nat) : (term310 _78901 k GEN_PVAR_181 i) = (term296 _78901 GEN_PVAR_181 k i).
Proof. exact (TRANS (@lem6194133 _78901 GEN_PVAR_181 k i) (@lem6194134 _78901 GEN_PVAR_181 k i)). Qed.
Lemma lem6194136 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term312 _78901 k GEN_PVAR_181) = (term298 _78901 GEN_PVAR_181 k).
Proof. exact (fun_ext (fun i : nat => @lem6194135 _78901 GEN_PVAR_181 k i)). Qed.
Lemma lem6194137 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6194138 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term313 _78901 k GEN_PVAR_181) = (term299 _78901 GEN_PVAR_181 k).
Proof. exact (MK_COMB (@lem6194137) (@lem6194136 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6194139 (_78901 : type1605) (k : nat) : (term314 _78901 k) = (term300 _78901 k).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6194138 _78901 GEN_PVAR_181 k)). Qed.
Lemma lem6194140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6194141 (_78901 : type1605) (k : nat) : (term306 _78901 k) = (term301 _78901 k).
Proof. exact (MK_COMB (@lem6194140) (@lem6194139 _78901 k)). Qed.
Lemma lem6194142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6194143 (_78901 : type1605) (k : nat) : (term315 _78901 k) = (term316 _78901 k).
Proof. exact (MK_COMB (@lem6194142) (@lem6194141 _78901 k)). Qed.
Lemma lem6194144 (_78901 : type1605) (GEN_PVAR_181 : nat) (k : nat) : (term309 _78901 k GEN_PVAR_181) = (term298 _78901 GEN_PVAR_181 k).
Proof. exact (eq_refl (term309 _78901 k GEN_PVAR_181)). Qed.
Lemma lem6194145 (i : nat -> nat) (GEN_PVAR_181 : nat) : (i GEN_PVAR_181) = (i GEN_PVAR_181).
Proof. exact (eq_refl (i GEN_PVAR_181)). Qed.
Lemma lem6194146 (_78901 : type1605) (k : nat) (i : nat -> nat) (GEN_PVAR_181 : nat) : (term317 _78901 k i GEN_PVAR_181) = (term318 _78901 k i GEN_PVAR_181).
Proof. exact (MK_COMB (@lem6194144 _78901 GEN_PVAR_181 k) (@lem6194145 i GEN_PVAR_181)). Qed.
Lemma lem6194147 (_78901 : type1605) (k : nat) (i : nat -> nat) (GEN_PVAR_181 : nat) : (term318 _78901 k i GEN_PVAR_181) = (term319 _78901 k i GEN_PVAR_181).
Proof. exact (eq_refl (term318 _78901 k i GEN_PVAR_181)). Qed.
Lemma lem6194148 (_78901 : type1605) (k : nat) (i : nat -> nat) (GEN_PVAR_181 : nat) : (term317 _78901 k i GEN_PVAR_181) = (term319 _78901 k i GEN_PVAR_181).
Proof. exact (TRANS (@lem6194146 _78901 k i GEN_PVAR_181) (@lem6194147 _78901 k i GEN_PVAR_181)). Qed.
Lemma lem6194149 (_78901 : type1605) (k : nat) (i : nat -> nat) : (term320 _78901 k i) = (term321 _78901 k i).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem6194148 _78901 k i GEN_PVAR_181)). Qed.
Lemma lem6194150 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6194151 (_78901 : type1605) (k : nat) (i : nat -> nat) : (term322 _78901 k i) = (term323 _78901 k i).
Proof. exact (MK_COMB (@lem6194150) (@lem6194149 _78901 k i)). Qed.
Lemma lem6194152 (_78901 : type1605) (k : nat) : (term324 _78901 k) = (term325 _78901 k).
Proof. exact (fun_ext (fun i : nat -> nat => @lem6194151 _78901 k i)). Qed.
Lemma lem6194153 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem6194154 (_78901 : type1605) (k : nat) : (term307 _78901 k) = (term326 _78901 k).
Proof. exact (MK_COMB (@lem6194153) (@lem6194152 _78901 k)). Qed.
Lemma lem6194155 (_78901 : type1605) (k : nat) : ((term306 _78901 k) = (term307 _78901 k)) = ((term301 _78901 k) = (term326 _78901 k)).
Proof. exact (MK_COMB (@lem6194143 _78901 k) (@lem6194154 _78901 k)). Qed.
Lemma lem6194156 (_78901 : type1605) (k : nat) : (term301 _78901 k) = (term326 _78901 k).
Proof. exact (EQ_MP (@lem6194155 _78901 k) (@lem6194130 _78901 k)). Qed.
Lemma lem6194157 (_78901 : type1605) (k : nat) : (term260 _78901 k) = (term326 _78901 k).
Proof. exact (TRANS (@lem6194126 _78901 k) (@lem6194156 _78901 k)). Qed.
Lemma lem6194158 (_78901 : type1605) : (term267 _78901) = (term327 _78901).
Proof. exact (fun_ext (fun k : nat => @lem6194157 _78901 k)). Qed.
Lemma lem6194159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6194160 (_78901 : type1605) : (term282 _78901) = (term328 _78901).
Proof. exact (MK_COMB (@lem6194159) (@lem6194158 _78901)). Qed.
Lemma lem6194162 {A B : Type'} (P : type1413 A B) : (term302 A B P) = (term303 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6194163 (P : type1586) : (term329 P) = (term330 P).
Proof. exact (@lem6194162 nat (nat -> nat) P). Qed.
Lemma lem6194164 (_78901 : type1605) : (term331 _78901) = (term332 _78901).
Proof. exact (@lem6194163 (term333 _78901)). Qed.
Lemma lem6194165 (_78901 : type1605) (k : nat) : (term334 _78901 k) = (term325 _78901 k).
Proof. exact (eq_refl (term334 _78901 k)). Qed.
Lemma lem6194166 (i : nat -> nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6194167 (_78901 : type1605) (k : nat) (i : nat -> nat) : (term335 _78901 k i) = (term336 _78901 k i).
Proof. exact (MK_COMB (@lem6194165 _78901 k) (@lem6194166 i)). Qed.
Lemma lem6194168 (_78901 : type1605) (k : nat) (i : nat -> nat) : (term336 _78901 k i) = (term323 _78901 k i).
Proof. exact (eq_refl (term336 _78901 k i)). Qed.
Lemma lem6194169 (_78901 : type1605) (k : nat) (i : nat -> nat) : (term335 _78901 k i) = (term323 _78901 k i).
Proof. exact (TRANS (@lem6194167 _78901 k i) (@lem6194168 _78901 k i)). Qed.
Lemma lem6194170 (_78901 : type1605) (k : nat) : (term337 _78901 k) = (term325 _78901 k).
Proof. exact (fun_ext (fun i : nat -> nat => @lem6194169 _78901 k i)). Qed.
Lemma lem6194171 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem6194172 (_78901 : type1605) (k : nat) : (term338 _78901 k) = (term326 _78901 k).
Proof. exact (MK_COMB (@lem6194171) (@lem6194170 _78901 k)). Qed.
Lemma lem6194173 (_78901 : type1605) : (term339 _78901) = (term327 _78901).
Proof. exact (fun_ext (fun k : nat => @lem6194172 _78901 k)). Qed.
Lemma lem6194174 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6194175 (_78901 : type1605) : (term331 _78901) = (term328 _78901).
Proof. exact (MK_COMB (@lem6194174) (@lem6194173 _78901)). Qed.
Lemma lem6194176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6194177 (_78901 : type1605) : (term340 _78901) = (term341 _78901).
Proof. exact (MK_COMB (@lem6194176) (@lem6194175 _78901)). Qed.
Lemma lem6194178 (_78901 : type1605) (k : nat) : (term334 _78901 k) = (term325 _78901 k).
Proof. exact (eq_refl (term334 _78901 k)). Qed.
Lemma lem6194179 (i : type1606) (k : nat) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem6194180 (_78901 : type1605) (i : type1606) (k : nat) : (term342 _78901 i k) = (term343 _78901 i k).
Proof. exact (MK_COMB (@lem6194178 _78901 k) (@lem6194179 i k)). Qed.
Lemma lem6194181 (_78901 : type1605) (i : type1606) (k : nat) : (term343 _78901 i k) = (term344 _78901 i k).
Proof. exact (eq_refl (term343 _78901 i k)). Qed.
Lemma lem6194182 (_78901 : type1605) (i : type1606) (k : nat) : (term342 _78901 i k) = (term344 _78901 i k).
Proof. exact (TRANS (@lem6194180 _78901 i k) (@lem6194181 _78901 i k)). Qed.
Lemma lem6194183 (_78901 : type1605) (i : type1606) : (term345 _78901 i) = (term346 _78901 i).
Proof. exact (fun_ext (fun k : nat => @lem6194182 _78901 i k)). Qed.
Lemma lem6194184 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6194185 (_78901 : type1605) (i : type1606) : (term347 _78901 i) = (term348 _78901 i).
Proof. exact (MK_COMB (@lem6194184) (@lem6194183 _78901 i)). Qed.
Lemma lem6194186 (_78901 : type1605) : (term349 _78901) = (term350 _78901).
Proof. exact (fun_ext (fun i : type1606 => @lem6194185 _78901 i)). Qed.
Lemma lem6194187 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem6194188 (_78901 : type1605) : (term332 _78901) = (term351 _78901).
Proof. exact (MK_COMB (@lem6194187) (@lem6194186 _78901)). Qed.
Lemma lem6194189 (_78901 : type1605) : ((term331 _78901) = (term332 _78901)) = ((term328 _78901) = (term351 _78901)).
Proof. exact (MK_COMB (@lem6194177 _78901) (@lem6194188 _78901)). Qed.
Lemma lem6194190 (_78901 : type1605) : (term328 _78901) = (term351 _78901).
Proof. exact (EQ_MP (@lem6194189 _78901) (@lem6194164 _78901)). Qed.
Lemma lem6194191 (_78901 : type1605) : (term282 _78901) = (term351 _78901).
Proof. exact (TRANS (@lem6194160 _78901) (@lem6194190 _78901)). Qed.
Lemma lem6194192 (_78901 : type1605) : (term279 _78901) = (term279 _78901).
Proof. exact (eq_refl (term279 _78901)). Qed.
Lemma lem6194193 (_78901 : type1605) : (term283 _78901) = (term352 _78901).
Proof. exact (MK_COMB (@lem6194192 _78901) (@lem6194191 _78901)). Qed.
Lemma lem6194195 {A : Type'} (P : Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6194196 (P : Prop) (Q : type961) : (term355 P Q) = (term356 P Q).
Proof. exact (@lem6194195 type1606 P Q). Qed.
Lemma lem6194197 (_78901 : type1605) : (term357 _78901) = (term358 _78901).
Proof. exact (@lem6194196 (term277 _78901) (term350 _78901)). Qed.
Lemma lem6194198 (_78901 : type1605) (i : type1606) : (term359 _78901 i) = (term348 _78901 i).
Proof. exact (eq_refl (term359 _78901 i)). Qed.
Lemma lem6194199 (_78901 : type1605) : (term360 _78901) = (term350 _78901).
Proof. exact (fun_ext (fun i : type1606 => @lem6194198 _78901 i)). Qed.
Lemma lem6194200 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem6194201 (_78901 : type1605) : (term361 _78901) = (term351 _78901).
Proof. exact (MK_COMB (@lem6194200) (@lem6194199 _78901)). Qed.
Lemma lem6194202 (_78901 : type1605) : (term279 _78901) = (term279 _78901).
Proof. exact (eq_refl (term279 _78901)). Qed.
Lemma lem6194203 (_78901 : type1605) : (term357 _78901) = (term352 _78901).
Proof. exact (MK_COMB (@lem6194202 _78901) (@lem6194201 _78901)). Qed.
Lemma lem6194204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6194205 (_78901 : type1605) : (term362 _78901) = (term363 _78901).
Proof. exact (MK_COMB (@lem6194204) (@lem6194203 _78901)). Qed.
Lemma lem6194206 (_78901 : type1605) (i : type1606) : (term359 _78901 i) = (term348 _78901 i).
Proof. exact (eq_refl (term359 _78901 i)). Qed.
Lemma lem6194207 (_78901 : type1605) : (term279 _78901) = (term279 _78901).
Proof. exact (eq_refl (term279 _78901)). Qed.
Lemma lem6194208 (_78901 : type1605) (i : type1606) : (term364 _78901 i) = (term365 _78901 i).
Proof. exact (MK_COMB (@lem6194207 _78901) (@lem6194206 _78901 i)). Qed.
Lemma lem6194209 (_78901 : type1605) : (term366 _78901) = (term367 _78901).
Proof. exact (fun_ext (fun i : type1606 => @lem6194208 _78901 i)). Qed.
Lemma lem6194210 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem6194211 (_78901 : type1605) : (term358 _78901) = (term368 _78901).
Proof. exact (MK_COMB (@lem6194210) (@lem6194209 _78901)). Qed.
Lemma lem6194212 (_78901 : type1605) : ((term357 _78901) = (term358 _78901)) = ((term352 _78901) = (term368 _78901)).
Proof. exact (MK_COMB (@lem6194205 _78901) (@lem6194211 _78901)). Qed.
Lemma lem6194213 (_78901 : type1605) : (term352 _78901) = (term368 _78901).
Proof. exact (EQ_MP (@lem6194212 _78901) (@lem6194197 _78901)). Qed.
Lemma lem6194214 (_78901 : type1605) : (term283 _78901) = (term368 _78901).
Proof. exact (TRANS (@lem6194193 _78901) (@lem6194213 _78901)). Qed.
Lemma lem6194215 (_78901 : type1605) : (term237 _78901) = (term368 _78901).
Proof. exact (TRANS (@lem6194103 _78901) (@lem6194214 _78901)). Qed.
Lemma lem6194216 (_78901 : type1605) : (term208 _78901) = (term368 _78901).
Proof. exact (TRANS (@lem6193825 _78901) (@lem6194215 _78901)). Qed.
Lemma lem6194217 (_78901 : type1605) (h1 : term208 _78901) : term368 _78901.
Proof. exact (EQ_MP (@lem6194216 _78901) (@lem6193785 _78901 h1)). Qed.
Lemma lem6194218 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (x : _123501) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem6194219 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term153 _123501 op x) = (term153 _123501 op x).
Proof. exact (fun_ext (fun y : _123501 => @lem6194218 _123501 op y x)). Qed.
Lemma lem6194220 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194221 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term154 _123501 op x) = (term154 _123501 op x).
Proof. exact (MK_COMB (@lem6194220 _123501) (@lem6194219 _123501 op x)). Qed.
Lemma lem6194222 {_123501 : Type'} (op : type1400 _123501) : (term155 _123501 op) = (term155 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6194221 _123501 op x)). Qed.
Lemma lem6194223 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194224 {_123501 : Type'} (op : type1400 _123501) : (term156 _123501 op) = (term156 _123501 op).
Proof. exact (MK_COMB (@lem6194223 _123501) (@lem6194222 _123501 op)). Qed.
Lemma lem6194225 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) (z : _123501) : ((term143 _123501 x op y z) = (term144 _123501 op x y z)) = ((term143 _123501 x op y z) = (term144 _123501 op x y z)).
Proof. exact (eq_refl ((term143 _123501 x op y z) = (term144 _123501 op x y z))). Qed.
Lemma lem6194226 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term145 _123501 op x y) = (term145 _123501 op x y).
Proof. exact (fun_ext (fun z : _123501 => @lem6194225 _123501 op x y z)). Qed.
Lemma lem6194227 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194228 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term146 _123501 op x y) = (term146 _123501 op x y).
Proof. exact (MK_COMB (@lem6194227 _123501) (@lem6194226 _123501 op x y)). Qed.
Lemma lem6194229 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term147 _123501 op x) = (term147 _123501 op x).
Proof. exact (fun_ext (fun y : _123501 => @lem6194228 _123501 op x y)). Qed.
Lemma lem6194230 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194231 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term148 _123501 op x) = (term148 _123501 op x).
Proof. exact (MK_COMB (@lem6194230 _123501) (@lem6194229 _123501 op x)). Qed.
Lemma lem6194232 {_123501 : Type'} (op : type1400 _123501) : (term149 _123501 op) = (term149 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6194231 _123501 op x)). Qed.
Lemma lem6194233 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194234 {_123501 : Type'} (op : type1400 _123501) : (term150 _123501 op) = (term150 _123501 op).
Proof. exact (MK_COMB (@lem6194233 _123501) (@lem6194232 _123501 op)). Qed.
Lemma lem6194235 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : ((term140 _123501 op x) = x) = ((term140 _123501 op x) = x).
Proof. exact (eq_refl ((term140 _123501 op x) = x)). Qed.
Lemma lem6194236 {_123501 : Type'} (op : type1400 _123501) : (term141 _123501 op) = (term141 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6194235 _123501 op x)). Qed.
Lemma lem6194237 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194238 {_123501 : Type'} (op : type1400 _123501) : (term142 _123501 op) = (term142 _123501 op).
Proof. exact (MK_COMB (@lem6194237 _123501) (@lem6194236 _123501 op)). Qed.
Lemma lem6194239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6194240 {_123501 : Type'} (op : type1400 _123501) : (term151 _123501 op) = (term151 _123501 op).
Proof. exact (MK_COMB (@lem6194239) (@lem6194234 _123501 op)). Qed.
Lemma lem6194241 {_123501 : Type'} (op : type1400 _123501) : (term152 _123501 op) = (term152 _123501 op).
Proof. exact (MK_COMB (@lem6194240 _123501 op) (@lem6194238 _123501 op)). Qed.
Lemma lem6194242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6194243 {_123501 : Type'} (op : type1400 _123501) : (term157 _123501 op) = (term157 _123501 op).
Proof. exact (MK_COMB (@lem6194242) (@lem6194224 _123501 op)). Qed.
Lemma lem6194272 {_123501 : Type'} (op : type1400 _123501) : (term1 _123501 op) = (term1 _123501 op).
Proof. exact (MK_COMB (@lem6194243 _123501 op) (@lem6194241 _123501 op)). Qed.
Lemma lem6194273 {_123501 : Type'} (op : type1400 _123501) (h1 : term1 _123501 op) : term1 _123501 op.
Proof. exact (EQ_MP (@lem6194272 _123501 op) (@lem6193786 _123501 op h1)). Qed.
Lemma lem6194279 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) (h1 : term214 _123501 op _78901 f k) : term214 _123501 op _78901 f k.
Proof. exact (h1). Qed.
Lemma lem6194281 {_123501 : Type'} : (@eq _123501) = (@eq _123501).
Proof. exact (eq_refl (@eq _123501)). Qed.
Lemma lem6194290 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194291 {_123501 : Type'} (f : type1400 _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501 -> _123501) f x).
Proof. exact (@lem6194290 _123501 (_123501 -> _123501) f x). Qed.
Lemma lem6194292 {_123501 : Type'} (op : type1400 _123501) : (term369 _123501 op) = (term370 _123501 op).
Proof. exact (@lem6194291 _123501 op (@neutral _123501 op)). Qed.
Lemma lem6194293 {_123501 : Type'} (x : _123501) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6194294 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term140 _123501 op x) = (term371 _123501 op x).
Proof. exact (MK_COMB (@lem6194292 _123501 op) (@lem6194293 _123501 x)). Qed.
Lemma lem6194296 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194297 {_123501 : Type'} (f : _123501 -> _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501) f x).
Proof. exact (@lem6194296 _123501 _123501 f x). Qed.
Lemma lem6194298 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term371 _123501 op x) = (term372 _123501 op x).
Proof. exact (@lem6194297 _123501 (term370 _123501 op) x). Qed.
Lemma lem6194300 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term140 _123501 op x) = (term372 _123501 op x).
Proof. exact (TRANS (@lem6194294 _123501 op x) (@lem6194298 _123501 op x)). Qed.
Lemma lem6194301 {_123501 : Type'} (x : _123501) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6194302 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term373 _123501 op x) = (term374 _123501 op x).
Proof. exact (MK_COMB (@lem6194281 _123501) (@lem6194300 _123501 op x)). Qed.
Lemma lem6194303 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : ((term140 _123501 op x) = x) = ((term372 _123501 op x) = x).
Proof. exact (MK_COMB (@lem6194302 _123501 op x) (@lem6194301 _123501 x)). Qed.
Lemma lem6194304 {_123501 : Type'} (op : type1400 _123501) : (term141 _123501 op) = (term375 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6194303 _123501 op x)). Qed.
Lemma lem6194305 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194306 {_123501 : Type'} (op : type1400 _123501) : (term142 _123501 op) = (term376 _123501 op).
Proof. exact (MK_COMB (@lem6194305 _123501) (@lem6194304 _123501 op)). Qed.
Lemma lem6194307 {_123501 : Type'} : (@eq _123501) = (@eq _123501).
Proof. exact (eq_refl (@eq _123501)). Qed.
Lemma lem6194316 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194317 {_123501 : Type'} (f : type1400 _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501 -> _123501) f x).
Proof. exact (@lem6194316 _123501 (_123501 -> _123501) f x). Qed.
Lemma lem6194318 {_123501 : Type'} (op : type1400 _123501) (y : _123501) : (op y) = (@I (_123501 -> _123501 -> _123501) op y).
Proof. exact (@lem6194317 _123501 op y). Qed.
Lemma lem6194319 {_123501 : Type'} (z : _123501) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6194320 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (z : _123501) : (op y z) = (@I (_123501 -> _123501 -> _123501) op y z).
Proof. exact (MK_COMB (@lem6194318 _123501 op y) (@lem6194319 _123501 z)). Qed.
Lemma lem6194322 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194323 {_123501 : Type'} (f : _123501 -> _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501) f x).
Proof. exact (@lem6194322 _123501 _123501 f x). Qed.
Lemma lem6194324 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (z : _123501) : (@I (_123501 -> _123501 -> _123501) op y z) = (term377 _123501 op y z).
Proof. exact (@lem6194323 _123501 (@I (_123501 -> _123501 -> _123501) op y) z). Qed.
Lemma lem6194326 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (z : _123501) : (op y z) = (term377 _123501 op y z).
Proof. exact (TRANS (@lem6194320 _123501 op y z) (@lem6194324 _123501 op y z)). Qed.
Lemma lem6194327 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (op x) = (op x).
Proof. exact (eq_refl (op x)). Qed.
Lemma lem6194328 {_123501 : Type'} (x : _123501) (op : type1400 _123501) (y : _123501) (z : _123501) : (term143 _123501 x op y z) = (term378 _123501 x op y z).
Proof. exact (MK_COMB (@lem6194327 _123501 op x) (@lem6194326 _123501 op y z)). Qed.
Lemma lem6194330 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194331 {_123501 : Type'} (f : type1400 _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501 -> _123501) f x).
Proof. exact (@lem6194330 _123501 (_123501 -> _123501) f x). Qed.
Lemma lem6194332 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (op x) = (@I (_123501 -> _123501 -> _123501) op x).
Proof. exact (@lem6194331 _123501 op x). Qed.
Lemma lem6194333 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (z : _123501) : (term377 _123501 op y z) = (term377 _123501 op y z).
Proof. exact (eq_refl (term377 _123501 op y z)). Qed.
Lemma lem6194334 {_123501 : Type'} (x : _123501) (op : type1400 _123501) (y : _123501) (z : _123501) : (term378 _123501 x op y z) = (term379 _123501 x op y z).
Proof. exact (MK_COMB (@lem6194332 _123501 op x) (@lem6194333 _123501 op y z)). Qed.
Lemma lem6194336 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194337 {_123501 : Type'} (f : _123501 -> _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501) f x).
Proof. exact (@lem6194336 _123501 _123501 f x). Qed.
Lemma lem6194338 {_123501 : Type'} (x : _123501) (op : type1400 _123501) (y : _123501) (z : _123501) : (term379 _123501 x op y z) = (term380 _123501 x op y z).
Proof. exact (@lem6194337 _123501 (@I (_123501 -> _123501 -> _123501) op x) (term377 _123501 op y z)). Qed.
Lemma lem6194339 {_123501 : Type'} (x : _123501) (op : type1400 _123501) (y : _123501) (z : _123501) : (term378 _123501 x op y z) = (term380 _123501 x op y z).
Proof. exact (TRANS (@lem6194334 _123501 x op y z) (@lem6194338 _123501 x op y z)). Qed.
Lemma lem6194340 {_123501 : Type'} (x : _123501) (op : type1400 _123501) (y : _123501) (z : _123501) : (term143 _123501 x op y z) = (term380 _123501 x op y z).
Proof. exact (TRANS (@lem6194328 _123501 x op y z) (@lem6194339 _123501 x op y z)). Qed.
Lemma lem6194341 {_123501 : Type'} (op : type1400 _123501) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6194348 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194349 {_123501 : Type'} (f : type1400 _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501 -> _123501) f x).
Proof. exact (@lem6194348 _123501 (_123501 -> _123501) f x). Qed.
Lemma lem6194350 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (op x) = (@I (_123501 -> _123501 -> _123501) op x).
Proof. exact (@lem6194349 _123501 op x). Qed.
Lemma lem6194351 {_123501 : Type'} (y : _123501) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6194352 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (op x y) = (@I (_123501 -> _123501 -> _123501) op x y).
Proof. exact (MK_COMB (@lem6194350 _123501 op x) (@lem6194351 _123501 y)). Qed.
Lemma lem6194354 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194355 {_123501 : Type'} (f : _123501 -> _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501) f x).
Proof. exact (@lem6194354 _123501 _123501 f x). Qed.
Lemma lem6194356 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (@I (_123501 -> _123501 -> _123501) op x y) = (term377 _123501 op x y).
Proof. exact (@lem6194355 _123501 (@I (_123501 -> _123501 -> _123501) op x) y). Qed.
Lemma lem6194358 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (op x y) = (term377 _123501 op x y).
Proof. exact (TRANS (@lem6194352 _123501 op x y) (@lem6194356 _123501 op x y)). Qed.
Lemma lem6194359 {_123501 : Type'} (z : _123501) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6194360 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term381 _123501 op x y) = (term382 _123501 op x y).
Proof. exact (MK_COMB (@lem6194341 _123501 op) (@lem6194358 _123501 op x y)). Qed.
Lemma lem6194361 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) (z : _123501) : (term144 _123501 op x y z) = (term383 _123501 op x y z).
Proof. exact (MK_COMB (@lem6194360 _123501 op x y) (@lem6194359 _123501 z)). Qed.
Lemma lem6194363 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194364 {_123501 : Type'} (f : type1400 _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501 -> _123501) f x).
Proof. exact (@lem6194363 _123501 (_123501 -> _123501) f x). Qed.
Lemma lem6194365 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term382 _123501 op x y) = (term384 _123501 op x y).
Proof. exact (@lem6194364 _123501 op (term377 _123501 op x y)). Qed.
Lemma lem6194366 {_123501 : Type'} (z : _123501) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6194367 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) (z : _123501) : (term383 _123501 op x y z) = (term385 _123501 op x y z).
Proof. exact (MK_COMB (@lem6194365 _123501 op x y) (@lem6194366 _123501 z)). Qed.
Lemma lem6194369 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194370 {_123501 : Type'} (f : _123501 -> _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501) f x).
Proof. exact (@lem6194369 _123501 _123501 f x). Qed.
Lemma lem6194371 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) (z : _123501) : (term385 _123501 op x y z) = (term386 _123501 op x y z).
Proof. exact (@lem6194370 _123501 (term384 _123501 op x y) z). Qed.
Lemma lem6194372 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) (z : _123501) : (term383 _123501 op x y z) = (term386 _123501 op x y z).
Proof. exact (TRANS (@lem6194367 _123501 op x y z) (@lem6194371 _123501 op x y z)). Qed.
Lemma lem6194373 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) (z : _123501) : (term144 _123501 op x y z) = (term386 _123501 op x y z).
Proof. exact (TRANS (@lem6194361 _123501 op x y z) (@lem6194372 _123501 op x y z)). Qed.
Lemma lem6194374 {_123501 : Type'} (x : _123501) (op : type1400 _123501) (y : _123501) (z : _123501) : (term387 _123501 x op y z) = (term388 _123501 x op y z).
Proof. exact (MK_COMB (@lem6194307 _123501) (@lem6194340 _123501 x op y z)). Qed.
Lemma lem6194375 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) (z : _123501) : ((term143 _123501 x op y z) = (term144 _123501 op x y z)) = ((term380 _123501 x op y z) = (term386 _123501 op x y z)).
Proof. exact (MK_COMB (@lem6194374 _123501 x op y z) (@lem6194373 _123501 op x y z)). Qed.
Lemma lem6194376 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term145 _123501 op x y) = (term389 _123501 op x y).
Proof. exact (fun_ext (fun z : _123501 => @lem6194375 _123501 op x y z)). Qed.
Lemma lem6194377 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194378 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term146 _123501 op x y) = (term390 _123501 op x y).
Proof. exact (MK_COMB (@lem6194377 _123501) (@lem6194376 _123501 op x y)). Qed.
Lemma lem6194379 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term147 _123501 op x) = (term391 _123501 op x).
Proof. exact (fun_ext (fun y : _123501 => @lem6194378 _123501 op x y)). Qed.
Lemma lem6194380 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194381 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term148 _123501 op x) = (term392 _123501 op x).
Proof. exact (MK_COMB (@lem6194380 _123501) (@lem6194379 _123501 op x)). Qed.
Lemma lem6194382 {_123501 : Type'} (op : type1400 _123501) : (term149 _123501 op) = (term393 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6194381 _123501 op x)). Qed.
Lemma lem6194383 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194384 {_123501 : Type'} (op : type1400 _123501) : (term150 _123501 op) = (term394 _123501 op).
Proof. exact (MK_COMB (@lem6194383 _123501) (@lem6194382 _123501 op)). Qed.
Lemma lem6194385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6194386 {_123501 : Type'} (op : type1400 _123501) : (term151 _123501 op) = (term395 _123501 op).
Proof. exact (MK_COMB (@lem6194385) (@lem6194384 _123501 op)). Qed.
Lemma lem6194387 {_123501 : Type'} (op : type1400 _123501) : (term152 _123501 op) = (term396 _123501 op).
Proof. exact (MK_COMB (@lem6194386 _123501 op) (@lem6194306 _123501 op)). Qed.
Lemma lem6194388 {_123501 : Type'} : (@eq _123501) = (@eq _123501).
Proof. exact (eq_refl (@eq _123501)). Qed.
Lemma lem6194395 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194396 {_123501 : Type'} (f : type1400 _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501 -> _123501) f x).
Proof. exact (@lem6194395 _123501 (_123501 -> _123501) f x). Qed.
Lemma lem6194397 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (op x) = (@I (_123501 -> _123501 -> _123501) op x).
Proof. exact (@lem6194396 _123501 op x). Qed.
Lemma lem6194398 {_123501 : Type'} (y : _123501) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6194399 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (op x y) = (@I (_123501 -> _123501 -> _123501) op x y).
Proof. exact (MK_COMB (@lem6194397 _123501 op x) (@lem6194398 _123501 y)). Qed.
Lemma lem6194401 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194402 {_123501 : Type'} (f : _123501 -> _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501) f x).
Proof. exact (@lem6194401 _123501 _123501 f x). Qed.
Lemma lem6194403 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (@I (_123501 -> _123501 -> _123501) op x y) = (term377 _123501 op x y).
Proof. exact (@lem6194402 _123501 (@I (_123501 -> _123501 -> _123501) op x) y). Qed.
Lemma lem6194405 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (op x y) = (term377 _123501 op x y).
Proof. exact (TRANS (@lem6194399 _123501 op x y) (@lem6194403 _123501 op x y)). Qed.
Lemma lem6194412 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194413 {_123501 : Type'} (f : type1400 _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501 -> _123501) f x).
Proof. exact (@lem6194412 _123501 (_123501 -> _123501) f x). Qed.
Lemma lem6194414 {_123501 : Type'} (op : type1400 _123501) (y : _123501) : (op y) = (@I (_123501 -> _123501 -> _123501) op y).
Proof. exact (@lem6194413 _123501 op y). Qed.
Lemma lem6194415 {_123501 : Type'} (x : _123501) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6194416 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (x : _123501) : (op y x) = (@I (_123501 -> _123501 -> _123501) op y x).
Proof. exact (MK_COMB (@lem6194414 _123501 op y) (@lem6194415 _123501 x)). Qed.
Lemma lem6194418 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194419 {_123501 : Type'} (f : _123501 -> _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501) f x).
Proof. exact (@lem6194418 _123501 _123501 f x). Qed.
Lemma lem6194420 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (x : _123501) : (@I (_123501 -> _123501 -> _123501) op y x) = (term377 _123501 op y x).
Proof. exact (@lem6194419 _123501 (@I (_123501 -> _123501 -> _123501) op y) x). Qed.
Lemma lem6194422 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (x : _123501) : (op y x) = (term377 _123501 op y x).
Proof. exact (TRANS (@lem6194416 _123501 op y x) (@lem6194420 _123501 op y x)). Qed.
Lemma lem6194423 {_123501 : Type'} (op : type1400 _123501) (x : _123501) (y : _123501) : (term397 _123501 op x y) = (term398 _123501 op x y).
Proof. exact (MK_COMB (@lem6194388 _123501) (@lem6194405 _123501 op x y)). Qed.
Lemma lem6194424 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (x : _123501) : ((op x y) = (op y x)) = ((term377 _123501 op x y) = (term377 _123501 op y x)).
Proof. exact (MK_COMB (@lem6194423 _123501 op x y) (@lem6194422 _123501 op y x)). Qed.
Lemma lem6194425 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term153 _123501 op x) = (term399 _123501 op x).
Proof. exact (fun_ext (fun y : _123501 => @lem6194424 _123501 op y x)). Qed.
Lemma lem6194426 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194427 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term154 _123501 op x) = (term400 _123501 op x).
Proof. exact (MK_COMB (@lem6194426 _123501) (@lem6194425 _123501 op x)). Qed.
Lemma lem6194428 {_123501 : Type'} (op : type1400 _123501) : (term155 _123501 op) = (term401 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6194427 _123501 op x)). Qed.
Lemma lem6194429 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194430 {_123501 : Type'} (op : type1400 _123501) : (term156 _123501 op) = (term402 _123501 op).
Proof. exact (MK_COMB (@lem6194429 _123501) (@lem6194428 _123501 op)). Qed.
Lemma lem6194431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6194432 {_123501 : Type'} (op : type1400 _123501) : (term157 _123501 op) = (term403 _123501 op).
Proof. exact (MK_COMB (@lem6194431) (@lem6194430 _123501 op)). Qed.
Lemma lem6194433 {_123501 : Type'} (op : type1400 _123501) : (term1 _123501 op) = (term404 _123501 op).
Proof. exact (MK_COMB (@lem6194432 _123501 op) (@lem6194387 _123501 op)). Qed.
Lemma lem6194434 {_123501 : Type'} (op : type1400 _123501) (h1 : term1 _123501 op) : term404 _123501 op.
Proof. exact (EQ_MP (@lem6194433 _123501 op) (@lem6194273 _123501 op h1)). Qed.
Lemma lem6194435 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6194436 {_123501 : Type'} : (@eq _123501) = (@eq _123501).
Proof. exact (eq_refl (@eq _123501)). Qed.
Lemma lem6194437 {_123501 : Type'} (op : type1400 _123501) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6194442 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194443 {_123501 : Type'} (f : nat -> _123501) (x : nat) : (f x) = (@I (nat -> _123501) f x).
Proof. exact (@lem6194442 nat _123501 f x). Qed.
Lemma lem6194445 {_123501 : Type'} (f : nat -> _123501) (k : nat) : (f k) = (@I (nat -> _123501) f k).
Proof. exact (@lem6194443 _123501 f k). Qed.
Lemma lem6194456 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (k : nat) (f : nat -> _123501) : (term131 _123501 op _78901 k f) = (term131 _123501 op _78901 k f).
Proof. exact (eq_refl (term131 _123501 op _78901 k f)). Qed.
Lemma lem6194457 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (k : nat) : (term135 _123501 op f k) = (term405 _123501 op f k).
Proof. exact (MK_COMB (@lem6194437 _123501 op) (@lem6194445 _123501 f k)). Qed.
Lemma lem6194458 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (k : nat) (f : nat -> _123501) : (term136 _123501 op _78901 k f) = (term406 _123501 op _78901 k f).
Proof. exact (MK_COMB (@lem6194457 _123501 op f k) (@lem6194456 _123501 op _78901 k f)). Qed.
Lemma lem6194460 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194461 {_123501 : Type'} (f : type1400 _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501 -> _123501) f x).
Proof. exact (@lem6194460 _123501 (_123501 -> _123501) f x). Qed.
Lemma lem6194462 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (k : nat) : (term405 _123501 op f k) = (term407 _123501 op f k).
Proof. exact (@lem6194461 _123501 op (@I (nat -> _123501) f k)). Qed.
Lemma lem6194463 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (k : nat) (f : nat -> _123501) : (term131 _123501 op _78901 k f) = (term131 _123501 op _78901 k f).
Proof. exact (eq_refl (term131 _123501 op _78901 k f)). Qed.
Lemma lem6194464 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (k : nat) (f : nat -> _123501) : (term406 _123501 op _78901 k f) = (term408 _123501 op _78901 k f).
Proof. exact (MK_COMB (@lem6194462 _123501 op f k) (@lem6194463 _123501 op _78901 k f)). Qed.
Lemma lem6194466 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194467 {_123501 : Type'} (f : _123501 -> _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501) f x).
Proof. exact (@lem6194466 _123501 _123501 f x). Qed.
Lemma lem6194468 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (k : nat) (f : nat -> _123501) : (term408 _123501 op _78901 k f) = (term409 _123501 op _78901 k f).
Proof. exact (@lem6194467 _123501 (term407 _123501 op f k) (term131 _123501 op _78901 k f)). Qed.
Lemma lem6194469 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (k : nat) (f : nat -> _123501) : (term406 _123501 op _78901 k f) = (term409 _123501 op _78901 k f).
Proof. exact (TRANS (@lem6194464 _123501 op _78901 k f) (@lem6194468 _123501 op _78901 k f)). Qed.
Lemma lem6194470 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (k : nat) (f : nat -> _123501) : (term136 _123501 op _78901 k f) = (term409 _123501 op _78901 k f).
Proof. exact (TRANS (@lem6194458 _123501 op _78901 k f) (@lem6194469 _123501 op _78901 k f)). Qed.
Lemma lem6194487 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194488 {_123501 : Type'} (f : nat -> _123501) (x : nat) : (f x) = (@I (nat -> _123501) f x).
Proof. exact (@lem6194487 nat _123501 f x). Qed.
Lemma lem6194490 {_123501 : Type'} (f : nat -> _123501) (k : nat) : (f k) = (@I (nat -> _123501) f k).
Proof. exact (@lem6194488 _123501 f k). Qed.
Lemma lem6194491 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (k : nat) (f : nat -> _123501) : (term133 _123501 op _78901 k f) = (term133 _123501 op _78901 k f).
Proof. exact (eq_refl (term133 _123501 op _78901 k f)). Qed.
Lemma lem6194492 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : (term134 _123501 op _78901 f k) = (term410 _123501 op _78901 f k).
Proof. exact (MK_COMB (@lem6194491 _123501 op _78901 k f) (@lem6194490 _123501 f k)). Qed.
Lemma lem6194494 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194495 {_123501 : Type'} (f : type1400 _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501 -> _123501) f x).
Proof. exact (@lem6194494 _123501 (_123501 -> _123501) f x). Qed.
Lemma lem6194496 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (k : nat) (f : nat -> _123501) : (term133 _123501 op _78901 k f) = (term411 _123501 op _78901 k f).
Proof. exact (@lem6194495 _123501 op (term131 _123501 op _78901 k f)). Qed.
Lemma lem6194497 {_123501 : Type'} (f : nat -> _123501) (k : nat) : (@I (nat -> _123501) f k) = (@I (nat -> _123501) f k).
Proof. exact (eq_refl (@I (nat -> _123501) f k)). Qed.
Lemma lem6194498 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : (term410 _123501 op _78901 f k) = (term412 _123501 op _78901 f k).
Proof. exact (MK_COMB (@lem6194496 _123501 op _78901 k f) (@lem6194497 _123501 f k)). Qed.
Lemma lem6194500 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6194501 {_123501 : Type'} (f : _123501 -> _123501) (x : _123501) : (f x) = (@I (_123501 -> _123501) f x).
Proof. exact (@lem6194500 _123501 _123501 f x). Qed.
Lemma lem6194502 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : (term412 _123501 op _78901 f k) = (term413 _123501 op _78901 f k).
Proof. exact (@lem6194501 _123501 (term411 _123501 op _78901 k f) (@I (nat -> _123501) f k)). Qed.
Lemma lem6194503 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : (term410 _123501 op _78901 f k) = (term413 _123501 op _78901 f k).
Proof. exact (TRANS (@lem6194498 _123501 op _78901 f k) (@lem6194502 _123501 op _78901 f k)). Qed.
Lemma lem6194504 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : (term134 _123501 op _78901 f k) = (term413 _123501 op _78901 f k).
Proof. exact (TRANS (@lem6194492 _123501 op _78901 f k) (@lem6194503 _123501 op _78901 f k)). Qed.
Lemma lem6194505 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (k : nat) (f : nat -> _123501) : (term137 _123501 op _78901 k f) = (term414 _123501 op _78901 k f).
Proof. exact (MK_COMB (@lem6194436 _123501) (@lem6194470 _123501 op _78901 k f)). Qed.
Lemma lem6194506 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : ((term136 _123501 op _78901 k f) = (term134 _123501 op _78901 f k)) = ((term409 _123501 op _78901 k f) = (term413 _123501 op _78901 f k)).
Proof. exact (MK_COMB (@lem6194505 _123501 op _78901 k f) (@lem6194504 _123501 op _78901 f k)). Qed.
Lemma lem6194507 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : (term214 _123501 op _78901 f k) = (term415 _123501 op _78901 f k).
Proof. exact (MK_COMB (@lem6194435) (@lem6194506 _123501 op _78901 f k)). Qed.
Lemma lem6194591 {_123501 : Type'} (op : type1400 _123501) (h1 : term1 _123501 op) : term402 _123501 op.
Proof. exact (proj1 (@lem6194434 _123501 op h1)). Qed.
Lemma lem6194659 {_123501 : Type'} (op : type1400 _123501) (y : _123501) (x : _123501) : ((term377 _123501 op x y) = (term377 _123501 op y x)) = ((term377 _123501 op x y) = (term377 _123501 op y x)).
Proof. exact (eq_refl ((term377 _123501 op x y) = (term377 _123501 op y x))). Qed.
Lemma lem6194660 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term399 _123501 op x) = (term399 _123501 op x).
Proof. exact (fun_ext (fun y : _123501 => @lem6194659 _123501 op y x)). Qed.
Lemma lem6194661 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194662 {_123501 : Type'} (op : type1400 _123501) (x : _123501) : (term400 _123501 op x) = (term400 _123501 op x).
Proof. exact (MK_COMB (@lem6194661 _123501) (@lem6194660 _123501 op x)). Qed.
Lemma lem6194663 {_123501 : Type'} (op : type1400 _123501) : (term401 _123501 op) = (term401 _123501 op).
Proof. exact (fun_ext (fun x : _123501 => @lem6194662 _123501 op x)). Qed.
Lemma lem6194664 {_123501 : Type'} : (@all _123501) = (@all _123501).
Proof. exact (eq_refl (@all _123501)). Qed.
Lemma lem6194666 {_123501 : Type'} (op : type1400 _123501) : (term402 _123501 op) = (term402 _123501 op).
Proof. exact (MK_COMB (@lem6194664 _123501) (@lem6194663 _123501 op)). Qed.
Lemma lem6194667 {_123501 : Type'} (op : type1400 _123501) (h1 : term1 _123501 op) : term402 _123501 op.
Proof. exact (EQ_MP (@lem6194666 _123501 op) (@lem6194591 _123501 op h1)). Qed.
Lemma lem6194703 {_123501 : Type'} (_78907 : _123501) (op : type1400 _123501) (h1 : term1 _123501 op) : term416 _123501 op _78907.
Proof. exact (@lem6194667 _123501 op h1 _78907). Qed.
Lemma lem6194704 {_123501 : Type'} (op : type1400 _123501) (_78907 : _123501) : (term416 _123501 op _78907) = (term400 _123501 op _78907).
Proof. exact (eq_refl (term416 _123501 op _78907)). Qed.
Lemma lem6194705 {_123501 : Type'} (_78907 : _123501) (op : type1400 _123501) (h1 : term1 _123501 op) : term400 _123501 op _78907.
Proof. exact (EQ_MP (@lem6194704 _123501 op _78907) (@lem6194703 _123501 _78907 op h1)). Qed.
Lemma lem6194706 {_123501 : Type'} (_78907 : _123501) (_78908 : _123501) (op : type1400 _123501) (h1 : term1 _123501 op) : term417 _123501 op _78907 _78908.
Proof. exact (@lem6194705 _123501 _78907 op h1 _78908). Qed.
Lemma lem6194707 {_123501 : Type'} (op : type1400 _123501) (_78908 : _123501) (_78907 : _123501) : (term417 _123501 op _78907 _78908) = ((term377 _123501 op _78907 _78908) = (term377 _123501 op _78908 _78907)).
Proof. exact (eq_refl (term417 _123501 op _78907 _78908)). Qed.
Lemma lem6194722 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) (h1 : term214 _123501 op _78901 f k) : term415 _123501 op _78901 f k.
Proof. exact (EQ_MP (@lem6194507 _123501 op _78901 f k) (@lem6194279 _123501 op _78901 f k h1)). Qed.
Lemma lem6194920 {_123501 : Type'} (_78908 : _123501) (_78907 : _123501) (op : type1400 _123501) (h1 : term1 _123501 op) : (term377 _123501 op _78907 _78908) = (term377 _123501 op _78908 _78907).
Proof. exact (EQ_MP (@lem6194707 _123501 op _78908 _78907) (@lem6194706 _123501 _78907 _78908 op h1)). Qed.
Lemma lem6194921 {_123501 : Type'} (_78908 : _123501) (_78907 : _123501) (op : type1400 _123501) (h1 : term1 _123501 op) : (term377 _123501 op _78907 _78908) = (term377 _123501 op _78908 _78907).
Proof. exact (@lem6194920 _123501 _78908 _78907 op h1). Qed.
Lemma lem6194922 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term1 _123501 op) : (term409 _123501 op _78901 k f) = (term413 _123501 op _78901 f k).
Proof. exact (@lem6194921 _123501 (term131 _123501 op _78901 k f) (@I (nat -> _123501) f k) op h1). Qed.
Lemma lem6194923 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term1 _123501 op) : term418 _123501 op _78901 f k.
Proof. exact (fun h0 : term415 _123501 op _78901 f k => @lem6194922 _123501 _78901 f k op h1). Qed.
Lemma lem6194925 (p : Prop) : (term419 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6194926 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : (term418 _123501 op _78901 f k) = ((term409 _123501 op _78901 k f) = (term413 _123501 op _78901 f k)).
Proof. exact (@lem6194925 ((term409 _123501 op _78901 k f) = (term413 _123501 op _78901 f k))). Qed.
Lemma lem6194927 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term1 _123501 op) : (term409 _123501 op _78901 k f) = (term413 _123501 op _78901 f k).
Proof. exact (EQ_MP (@lem6194926 _123501 op _78901 f k) (@lem6194923 _123501 _78901 f k op h1)). Qed.
Lemma lem6194930 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6194932 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) : (term415 _123501 op _78901 f k) = (term420 _123501 op _78901 f k).
Proof. exact (@lem6194930 ((term409 _123501 op _78901 k f) = (term413 _123501 op _78901 f k))). Qed.
Lemma lem6194935 {_123501 : Type'} (op : type1400 _123501) (_78901 : type1605) (f : nat -> _123501) (k : nat) (h1 : term214 _123501 op _78901 f k) : term420 _123501 op _78901 f k.
Proof. exact (EQ_MP (@lem6194932 _123501 op _78901 f k) (@lem6194722 _123501 op _78901 f k h1)). Qed.
Lemma lem6194938 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term214 _123501 op _78901 f k) (h2 : term1 _123501 op) : False.
Proof. exact (@lem6194935 _123501 op _78901 f k h1 (@lem6194927 _123501 _78901 f k op h2)). Qed.
Lemma lem6194939 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term214 _123501 op _78901 f k) (h2 : term1 _123501 op) : term421.
Proof. exact (fun h0 : ~ False => @lem6194938 _123501 _78901 f k op h1 h2). Qed.
Lemma lem6194941 (p : Prop) : (term419 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6194942 : term421 = False.
Proof. exact (@lem6194941 False). Qed.
Lemma lem6194943 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term214 _123501 op _78901 f k) (h2 : term1 _123501 op) : False.
Proof. exact (EQ_MP (@lem6194942) (@lem6194939 _123501 _78901 f k op h1 h2)). Qed.
Lemma lem6194944 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term208 _78901) (h2 : term214 _123501 op _78901 f k) (h3 : term1 _123501 op) : False.
Proof. exact (ex_elim (@lem6194217 _78901 h1) (fun i : type1606 => fun h0 : term367 _78901 i => @lem6194943 _123501 _78901 f k op h2 h3)). Qed.
Lemma lem6194945 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term208 _78901) (h2 : term214 _123501 op _78901 f k) (h3 : term1 _123501 op) : (term214 _123501 op _78901 f k) = False.
Proof. exact (prop_ext (fun h4 : term214 _123501 op _78901 f k => @lem6194944 _123501 _78901 f k op h1 h2 h3) (fun h4 : False => @lem6194279 _123501 op _78901 f k h2)). Qed.
Lemma lem6194946 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term208 _78901) (h2 : term214 _123501 op _78901 f k) (h3 : term1 _123501 op) : False.
Proof. exact (EQ_MP (@lem6194945 _123501 _78901 f k op h1 h2 h3) (@lem6194279 _123501 op _78901 f k h2)). Qed.
Lemma lem6194947 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term208 _78901) (h2 : term214 _123501 op _78901 f k) (h3 : term1 _123501 op) : (term1 _123501 op) = False.
Proof. exact (prop_ext (fun h4 : term1 _123501 op => @lem6194946 _123501 _78901 f k op h1 h2 h3) (fun h4 : False => @lem6194273 _123501 op h3)). Qed.
Lemma lem6194948 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term208 _78901) (h2 : term214 _123501 op _78901 f k) (h3 : term1 _123501 op) : False.
Proof. exact (EQ_MP (@lem6194947 _123501 _78901 f k op h1 h2 h3) (@lem6194273 _123501 op h3)). Qed.
Lemma lem6194949 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term208 _78901) (h2 : term214 _123501 op _78901 f k) (h3 : term1 _123501 op) : (term214 _123501 op _78901 f k) = False.
Proof. exact (prop_ext (fun h4 : term214 _123501 op _78901 f k => @lem6194948 _123501 _78901 f k op h1 h2 h3) (fun h4 : False => @lem6193791 _123501 op _78901 f k h2)). Qed.
Lemma lem6194950 {_123501 : Type'} (_78901 : type1605) (f : nat -> _123501) (k : nat) (op : type1400 _123501) (h1 : term208 _78901) (h2 : term214 _123501 op _78901 f k) (h3 : term1 _123501 op) : False.
Proof. exact (EQ_MP (@lem6194949 _123501 _78901 f k op h1 h2 h3) (@lem6193791 _123501 op _78901 f k h2)). Qed.
Lemma lem6194951 {_123501 : Type'} (f : nat -> _123501) (k : nat) (_78901 : type1605) (op : type1400 _123501) (h1 : term208 _78901) (h2 : term1 _123501 op) : term213 _123501 op _78901 f k.
Proof. exact (fun h0 : term214 _123501 op _78901 f k => @lem6194950 _123501 _78901 f k op h1 h0 h2). Qed.
Lemma lem6194952 {_123501 : Type'} (f : nat -> _123501) (k : nat) (_78901 : type1605) (op : type1400 _123501) (h1 : term208 _78901) (h2 : term1 _123501 op) : (term136 _123501 op _78901 k f) = (term134 _123501 op _78901 f k).
Proof. exact (EQ_MP (@lem6193790 _123501 op _78901 f k) (@lem6194951 _123501 f k _78901 op h1 h2)). Qed.
Lemma lem6194957 {_123501 : Type'} (f : nat -> _123501) (_78901 : type1605) (op : type1400 _123501) (h1 : term208 _78901) (h2 : term1 _123501 op) : term139 _123501 op _78901 f.
Proof. exact (fun k : nat => @lem6194952 _123501 f k _78901 op h1 h2). Qed.
Lemma lem6194958 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) (_78901 : type1605) (h1 : term208 _78901) : term158 _123501 op _78901 f.
Proof. exact (fun h0 : term1 _123501 op => @lem6194957 _123501 f _78901 op h1 h0). Qed.
Lemma lem6194963 {_123501 : Type'} (f : nat -> _123501) (_78901 : type1605) (h1 : term208 _78901) : term160 _123501 _78901 f.
Proof. exact (fun op : type1400 _123501 => @lem6194958 _123501 op f _78901 h1). Qed.
Lemma lem6194968 {_123501 : Type'} (_78901 : type1605) (h1 : term208 _78901) : term162 _123501 _78901.
Proof. exact (fun f : nat -> _123501 => @lem6194963 _123501 f _78901 h1). Qed.
Lemma lem6194969 {_123501 : Type'} (_78901 : type1605) : term210 _123501 _78901.
Proof. exact (fun h0 : term208 _78901 => @lem6194968 _123501 _78901 h0). Qed.
Lemma lem6194974 {_123501 : Type'} : term212 _123501.
Proof. exact (fun _78901 : type1605 => @lem6194969 _123501 _78901). Qed.
Lemma lem6194975 {_123501 : Type'} : term123 _123501.
Proof. exact (EQ_MP (@lem6193784 _123501) (@lem6194974 _123501)). Qed.
Lemma lem6194976 {_123501 : Type'} (f : nat -> _123501) : term422 _123501 f.
Proof. exact (@lem6194975 _123501 f). Qed.
Lemma lem6194977 {_123501 : Type'} (f : nat -> _123501) : (term422 _123501 f) = (term114 _123501 f).
Proof. exact (eq_refl (term422 _123501 f)). Qed.
Lemma lem6194978 {_123501 : Type'} (f : nat -> _123501) : term114 _123501 f.
Proof. exact (EQ_MP (@lem6194977 _123501 f) (@lem6194976 _123501 f)). Qed.
Lemma lem6194980 {_123501 : Type'} (f : nat -> _123501) : term114 _123501 f.
Proof. exact (@lem6193359 _123501 f (@lem6194978 _123501 f)). Qed.
Lemma lem6194981 {_123501 : Type'} (f : nat -> _123501) (h1 : term115 _123501 f) : False.
Proof. exact (@lem6194980 _123501 f (@lem6193343 _123501 f h1)). Qed.
Lemma lem6194982 {_123501 : Type'} (f : nat -> _123501) (h1 : term115 _123501 f) : (term115 _123501 f) = False.
Proof. exact (prop_ext (fun h2 : term115 _123501 f => @lem6194981 _123501 f h1) (fun h2 : False => @lem6193343 _123501 f h1)). Qed.
Lemma lem6194983 {_123501 : Type'} (f : nat -> _123501) (h1 : term115 _123501 f) : False.
Proof. exact (EQ_MP (@lem6194982 _123501 f h1) (@lem6193343 _123501 f h1)). Qed.
Lemma lem6194984 {_123501 : Type'} (f : nat -> _123501) : term114 _123501 f.
Proof. exact (fun h0 : term115 _123501 f => @lem6194983 _123501 f h0). Qed.
Lemma lem6194985 {_123501 : Type'} (f : nat -> _123501) : term112 _123501 f.
Proof. exact (EQ_MP (@lem6193342 _123501 f) (@lem6194984 _123501 f)). Qed.
Lemma lem6194986 {_123501 : Type'} (f : nat -> _123501) : term79 _123501 f.
Proof. exact (EQ_MP (@lem6193338 _123501 f) (@lem6194985 _123501 f)). Qed.
Lemma lem6194987 {_123501 : Type'} (f : nat -> _123501) : term78 _123501 f.
Proof. exact (EQ_MP (@lem6193202 _123501 f) (@lem6194986 _123501 f)). Qed.
