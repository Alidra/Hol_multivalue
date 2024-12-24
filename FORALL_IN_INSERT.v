Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_IN_INSERT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import IN_INSERT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3206148 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3206149 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3206150 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3206149 A x) (@lem3206148 A x)). Qed.
Lemma lem3206151 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem3206150 A x y). Qed.
Lemma lem3206152 {A : Type'} (y : A) (x : A) : (term2 A x y) = (term3 A y x).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem3206153 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (EQ_MP (@lem3206152 A y x) (@lem3206151 A x y)). Qed.
Lemma lem3206154 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term4 A y x s.
Proof. exact (@lem3206153 A y x s). Qed.
Lemma lem3206155 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term4 A y x s) = ((term5 A x y s) = (term6 A y x s)).
Proof. exact (eq_refl (term4 A y x s)). Qed.
Lemma lem3206178 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (EQ_MP (@lem3206155 A y x s) (@lem3206154 A y x s)). Qed.
Lemma lem3206179 {_83983 : Type'} (y : _83983) (x : _83983) (s : _83983 -> Prop) : (term5 _83983 x y s) = (term6 _83983 y x s).
Proof. exact (@lem3206178 _83983 y x s). Qed.
Lemma lem3206180 {_83983 : Type'} (a : _83983) (x : _83983) (s : _83983 -> Prop) : (term5 _83983 x a s) = (term6 _83983 a x s).
Proof. exact (@lem3206179 _83983 a x s). Qed.
Lemma lem3206185 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3206186 {_83983 : Type'} (a : _83983) (x : _83983) (s : _83983 -> Prop) : (term7 _83983 x a s) = (term8 _83983 a x s).
Proof. exact (MK_COMB (@lem3206185) (@lem3206180 _83983 a x s)). Qed.
Lemma lem3206187 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3206188 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term9 _83983 a s P x) = (term10 _83983 a s P x).
Proof. exact (MK_COMB (@lem3206186 _83983 a x s) (@lem3206187 _83983 P x)). Qed.
Lemma lem3206191 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term11 _83983 a s P) = (term12 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206188 _83983 a s P x)). Qed.
Lemma lem3206192 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206193 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term13 _83983 a s P) = (term14 _83983 a s P).
Proof. exact (MK_COMB (@lem3206192 _83983) (@lem3206191 _83983 a s P)). Qed.
Lemma lem3206198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3206199 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term15 _83983 a s P) = (term16 _83983 a s P).
Proof. exact (MK_COMB (@lem3206198) (@lem3206193 _83983 a s P)). Qed.
Lemma lem3206208 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term17 _83983 a s P) = (term17 _83983 a s P).
Proof. exact (eq_refl (term17 _83983 a s P)). Qed.
Lemma lem3206209 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : ((term13 _83983 a s P) = (term17 _83983 a s P)) = ((term14 _83983 a s P) = (term17 _83983 a s P)).
Proof. exact (MK_COMB (@lem3206199 _83983 a s P) (@lem3206208 _83983 a s P)). Qed.
Lemma lem3206212 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term18 _83983 a P) = (term19 _83983 a P).
Proof. exact (fun_ext (fun s : _83983 -> Prop => @lem3206209 _83983 a s P)). Qed.
Lemma lem3206213 {_83983 : Type'} : (@all (_83983 -> Prop)) = (@all (_83983 -> Prop)).
Proof. exact (eq_refl (@all (_83983 -> Prop))). Qed.
Lemma lem3206214 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term20 _83983 a P) = (term21 _83983 a P).
Proof. exact (MK_COMB (@lem3206213 _83983) (@lem3206212 _83983 a P)). Qed.
Lemma lem3206219 {_83983 : Type'} (P : _83983 -> Prop) : (term22 _83983 P) = (term23 _83983 P).
Proof. exact (fun_ext (fun a : _83983 => @lem3206214 _83983 a P)). Qed.
Lemma lem3206220 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206221 {_83983 : Type'} (P : _83983 -> Prop) : (term24 _83983 P) = (term25 _83983 P).
Proof. exact (MK_COMB (@lem3206220 _83983) (@lem3206219 _83983 P)). Qed.
Lemma lem3206226 {_83983 : Type'} : (term26 _83983) = (term27 _83983).
Proof. exact (fun_ext (fun P : _83983 -> Prop => @lem3206221 _83983 P)). Qed.
Lemma lem3206227 {_83983 : Type'} : (@all (_83983 -> Prop)) = (@all (_83983 -> Prop)).
Proof. exact (eq_refl (@all (_83983 -> Prop))). Qed.
Lemma lem3206228 {_83983 : Type'} : (term28 _83983) = (term29 _83983).
Proof. exact (MK_COMB (@lem3206227 _83983) (@lem3206226 _83983)). Qed.
Lemma lem3206233 {_83983 : Type'} : (term29 _83983) = (term28 _83983).
Proof. exact (SYM (@lem3206228 _83983)). Qed.
Lemma lem3206235 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3206236 {_83983 : Type'} : (term29 _83983) = (term31 _83983).
Proof. exact (@lem3206235 (term29 _83983)). Qed.
Lemma lem3206237 {_83983 : Type'} : (term31 _83983) = (term29 _83983).
Proof. exact (SYM (@lem3206236 _83983)). Qed.
Lemma lem3206238 {_83983 : Type'} (h1 : term32 _83983) : term32 _83983.
Proof. exact (h1). Qed.
Lemma lem3206241 {_83983 : Type'} (h1 : term31 _83983) : term31 _83983.
Proof. exact (h1). Qed.
Lemma lem3206242 {_83983 : Type'} : term33 _83983.
Proof. exact (fun h0 : term31 _83983 => @lem3206241 _83983 h0). Qed.
Lemma lem3206243 {_83983 : Type'} (h1 : term33 _83983) : term33 _83983.
Proof. exact (h1). Qed.
Lemma lem3206244 {_83983 : Type'} (h1 : term31 _83983) : term31 _83983.
Proof. exact (h1). Qed.
Lemma lem3206245 {_83983 : Type'} (h1 : term31 _83983) (h2 : term33 _83983) : term31 _83983.
Proof. exact (@lem3206243 _83983 h2 (@lem3206244 _83983 h1)). Qed.
Lemma lem3206246 {_83983 : Type'} (h1 : term31 _83983) : term34 _83983.
Proof. exact (fun h0 : term33 _83983 => @lem3206245 _83983 h1 h0). Qed.
Lemma lem3206247 {_83983 : Type'} (h1 : term33 _83983) : term33 _83983.
Proof. exact (h1). Qed.
Lemma lem3206248 {_83983 : Type'} (h1 : term31 _83983) (h2 : term33 _83983) : term31 _83983.
Proof. exact (@lem3206246 _83983 h1 (@lem3206247 _83983 h2)). Qed.
Lemma lem3206249 {_83983 : Type'} (h1 : term33 _83983) : term33 _83983.
Proof. exact (fun h0 : term31 _83983 => @lem3206248 _83983 h0 h1). Qed.
Lemma lem3206250 {_83983 : Type'} : term35 _83983.
Proof. exact (fun h0 : term33 _83983 => @lem3206249 _83983 h0). Qed.
Lemma lem3206253 {_83983 : Type'} : term33 _83983.
Proof. exact (@lem3206250 _83983 (@lem3206242 _83983)). Qed.
Lemma lem3206254 {_83983 : Type'} : term33 _83983.
Proof. exact (@lem3206253 _83983). Qed.
Lemma lem3206256 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3206257 {_83983 : Type'} : (term31 _83983) = (term36 _83983).
Proof. exact (@lem3206256 (term32 _83983)). Qed.
Lemma lem3206259 (t : Prop) : (term37 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3206260 {_83983 : Type'} : (term36 _83983) = (term29 _83983).
Proof. exact (@lem3206259 (term29 _83983)). Qed.
Lemma lem3206293 {_83983 : Type'} : (term31 _83983) = (term29 _83983).
Proof. exact (TRANS (@lem3206257 _83983) (@lem3206260 _83983)). Qed.
Lemma lem3206298 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term38 _83983 s P x) = (term38 _83983 s P x).
Proof. exact (eq_refl (term38 _83983 s P x)). Qed.
Lemma lem3206299 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term39 _83983 s P) = (term39 _83983 s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206298 _83983 s P x)). Qed.
Lemma lem3206300 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206301 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term40 _83983 s P) = (term40 _83983 s P).
Proof. exact (MK_COMB (@lem3206300 _83983) (@lem3206299 _83983 s P)). Qed.
Lemma lem3206304 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term41 _83983 P a) = (term41 _83983 P a).
Proof. exact (eq_refl (term41 _83983 P a)). Qed.
Lemma lem3206305 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term17 _83983 a s P) = (term17 _83983 a s P).
Proof. exact (MK_COMB (@lem3206304 _83983 P a) (@lem3206301 _83983 s P)). Qed.
Lemma lem3206314 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term10 _83983 a s P x) = (term10 _83983 a s P x).
Proof. exact (eq_refl (term10 _83983 a s P x)). Qed.
Lemma lem3206315 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term12 _83983 a s P) = (term12 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206314 _83983 a s P x)). Qed.
Lemma lem3206316 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206317 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term14 _83983 a s P) = (term14 _83983 a s P).
Proof. exact (MK_COMB (@lem3206316 _83983) (@lem3206315 _83983 a s P)). Qed.
Lemma lem3206318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3206319 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term16 _83983 a s P) = (term16 _83983 a s P).
Proof. exact (MK_COMB (@lem3206318) (@lem3206317 _83983 a s P)). Qed.
Lemma lem3206320 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : ((term14 _83983 a s P) = (term17 _83983 a s P)) = ((term14 _83983 a s P) = (term17 _83983 a s P)).
Proof. exact (MK_COMB (@lem3206319 _83983 a s P) (@lem3206305 _83983 a s P)). Qed.
Lemma lem3206321 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term19 _83983 a P) = (term19 _83983 a P).
Proof. exact (fun_ext (fun s : _83983 -> Prop => @lem3206320 _83983 a s P)). Qed.
Lemma lem3206322 {_83983 : Type'} : (@all (_83983 -> Prop)) = (@all (_83983 -> Prop)).
Proof. exact (eq_refl (@all (_83983 -> Prop))). Qed.
Lemma lem3206323 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term21 _83983 a P) = (term21 _83983 a P).
Proof. exact (MK_COMB (@lem3206322 _83983) (@lem3206321 _83983 a P)). Qed.
Lemma lem3206324 {_83983 : Type'} (P : _83983 -> Prop) : (term23 _83983 P) = (term23 _83983 P).
Proof. exact (fun_ext (fun a : _83983 => @lem3206323 _83983 a P)). Qed.
Lemma lem3206325 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206326 {_83983 : Type'} (P : _83983 -> Prop) : (term25 _83983 P) = (term25 _83983 P).
Proof. exact (MK_COMB (@lem3206325 _83983) (@lem3206324 _83983 P)). Qed.
Lemma lem3206327 {_83983 : Type'} : (term27 _83983) = (term27 _83983).
Proof. exact (fun_ext (fun P : _83983 -> Prop => @lem3206326 _83983 P)). Qed.
Lemma lem3206328 {_83983 : Type'} : (@all (_83983 -> Prop)) = (@all (_83983 -> Prop)).
Proof. exact (eq_refl (@all (_83983 -> Prop))). Qed.
Lemma lem3206329 {_83983 : Type'} : (term29 _83983) = (term29 _83983).
Proof. exact (MK_COMB (@lem3206328 _83983) (@lem3206327 _83983)). Qed.
Lemma lem3206370 {_83983 : Type'} : (term31 _83983) = (term29 _83983).
Proof. exact (TRANS (@lem3206293 _83983) (@lem3206329 _83983)). Qed.
Lemma lem3206371 {_83983 : Type'} : (term29 _83983) = (term31 _83983).
Proof. exact (SYM (@lem3206370 _83983)). Qed.
Lemma lem3206373 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3206374 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : ((term14 _83983 a s P) = (term17 _83983 a s P)) = (term42 _83983 a s P).
Proof. exact (@lem3206373 ((term14 _83983 a s P) = (term17 _83983 a s P))). Qed.
Lemma lem3206375 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term42 _83983 a s P) = ((term14 _83983 a s P) = (term17 _83983 a s P)).
Proof. exact (SYM (@lem3206374 _83983 a s P)). Qed.
Lemma lem3206376 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term43 _83983 a s P) : term43 _83983 a s P.
Proof. exact (h1). Qed.
Lemma lem3206385 {_83983 : Type'} (a : _83983) (x : _83983) (s : _83983 -> Prop) : (term44 _83983 a x s) = (term45 _83983 a x s).
Proof. exact (@lem17160 (x = a) (@IN _83983 x s)). Qed.
Lemma lem3206390 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3206395 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term46 _83983 a s P x) = (term47 _83983 a s P x).
Proof. exact (@lem17362 (term6 _83983 a x s) (P x)). Qed.
Lemma lem3206396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3206397 {_83983 : Type'} (a : _83983) (x : _83983) (s : _83983 -> Prop) : (term48 _83983 a x s) = (term49 _83983 a x s).
Proof. exact (MK_COMB (@lem3206396) (@lem3206385 _83983 a x s)). Qed.
Lemma lem3206398 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term50 _83983 a s P x) = (term51 _83983 a s P x).
Proof. exact (MK_COMB (@lem3206397 _83983 a x s) (@lem3206390 _83983 P x)). Qed.
Lemma lem3206399 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term10 _83983 a s P x) = (term50 _83983 a s P x).
Proof. exact (@lem17265 (term6 _83983 a x s) (P x)). Qed.
Lemma lem3206400 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term10 _83983 a s P x) = (term51 _83983 a s P x).
Proof. exact (TRANS (@lem3206399 _83983 a s P x) (@lem3206398 _83983 a s P x)). Qed.
Lemma lem3206401 {_83983 : Type'} (P : _83983 -> Prop) : (term52 _83983 P) = (term53 _83983 P).
Proof. exact (@lem18392 _83983 P). Qed.
Lemma lem3206402 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term54 _83983 a s P) = (term55 _83983 a s P).
Proof. exact (@lem3206401 _83983 (term12 _83983 a s P)). Qed.
Lemma lem3206403 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term56 _83983 a s P x) = (term10 _83983 a s P x).
Proof. exact (eq_refl (term56 _83983 a s P x)). Qed.
Lemma lem3206404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3206405 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term57 _83983 a s P x) = (term46 _83983 a s P x).
Proof. exact (MK_COMB (@lem3206404) (@lem3206403 _83983 a s P x)). Qed.
Lemma lem3206406 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term57 _83983 a s P x) = (term47 _83983 a s P x).
Proof. exact (TRANS (@lem3206405 _83983 a s P x) (@lem3206395 _83983 a s P x)). Qed.
Lemma lem3206407 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term58 _83983 a s P) = (term59 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206406 _83983 a s P x)). Qed.
Lemma lem3206408 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206409 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term55 _83983 a s P) = (term60 _83983 a s P).
Proof. exact (MK_COMB (@lem3206408 _83983) (@lem3206407 _83983 a s P)). Qed.
Lemma lem3206410 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term54 _83983 a s P) = (term60 _83983 a s P).
Proof. exact (TRANS (@lem3206402 _83983 a s P) (@lem3206409 _83983 a s P)). Qed.
Lemma lem3206411 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term12 _83983 a s P) = (term61 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206400 _83983 a s P x)). Qed.
Lemma lem3206412 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206413 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term14 _83983 a s P) = (term62 _83983 a s P).
Proof. exact (MK_COMB (@lem3206412 _83983) (@lem3206411 _83983 a s P)). Qed.
Lemma lem3206424 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term63 _83983 s P x) = (term64 _83983 s P x).
Proof. exact (@lem17362 (@IN _83983 x s) (P x)). Qed.
Lemma lem3206429 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term38 _83983 s P x) = (term65 _83983 s P x).
Proof. exact (@lem17265 (@IN _83983 x s) (P x)). Qed.
Lemma lem3206430 {_83983 : Type'} (P : _83983 -> Prop) : (term52 _83983 P) = (term53 _83983 P).
Proof. exact (@lem18392 _83983 P). Qed.
Lemma lem3206431 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term66 _83983 s P) = (term67 _83983 s P).
Proof. exact (@lem3206430 _83983 (term39 _83983 s P)). Qed.
Lemma lem3206432 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term68 _83983 s P x) = (term38 _83983 s P x).
Proof. exact (eq_refl (term68 _83983 s P x)). Qed.
Lemma lem3206433 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3206434 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term69 _83983 s P x) = (term63 _83983 s P x).
Proof. exact (MK_COMB (@lem3206433) (@lem3206432 _83983 s P x)). Qed.
Lemma lem3206435 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term69 _83983 s P x) = (term64 _83983 s P x).
Proof. exact (TRANS (@lem3206434 _83983 s P x) (@lem3206424 _83983 s P x)). Qed.
Lemma lem3206436 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term70 _83983 s P) = (term71 _83983 s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206435 _83983 s P x)). Qed.
Lemma lem3206437 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206438 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term67 _83983 s P) = (term72 _83983 s P).
Proof. exact (MK_COMB (@lem3206437 _83983) (@lem3206436 _83983 s P)). Qed.
Lemma lem3206439 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term66 _83983 s P) = (term72 _83983 s P).
Proof. exact (TRANS (@lem3206431 _83983 s P) (@lem3206438 _83983 s P)). Qed.
Lemma lem3206440 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term39 _83983 s P) = (term73 _83983 s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206429 _83983 s P x)). Qed.
Lemma lem3206441 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206442 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term40 _83983 s P) = (term74 _83983 s P).
Proof. exact (MK_COMB (@lem3206441 _83983) (@lem3206440 _83983 s P)). Qed.
Lemma lem3206444 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term75 _83983 P a) = (term75 _83983 P a).
Proof. exact (eq_refl (term75 _83983 P a)). Qed.
Lemma lem3206445 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term76 _83983 a s P) = (term77 _83983 a s P).
Proof. exact (MK_COMB (@lem3206444 _83983 P a) (@lem3206439 _83983 s P)). Qed.
Lemma lem3206446 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term78 _83983 a s P) = (term76 _83983 a s P).
Proof. exact (@lem17045 (P a) (term40 _83983 s P)). Qed.
Lemma lem3206447 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term78 _83983 a s P) = (term77 _83983 a s P).
Proof. exact (TRANS (@lem3206446 _83983 a s P) (@lem3206445 _83983 a s P)). Qed.
Lemma lem3206449 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term41 _83983 P a) = (term41 _83983 P a).
Proof. exact (eq_refl (term41 _83983 P a)). Qed.
Lemma lem3206450 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term17 _83983 a s P) = (term79 _83983 a s P).
Proof. exact (MK_COMB (@lem3206449 _83983 P a) (@lem3206442 _83983 s P)). Qed.
Lemma lem3206451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3206452 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term80 _83983 a s P) = (term81 _83983 a s P).
Proof. exact (MK_COMB (@lem3206451) (@lem3206410 _83983 a s P)). Qed.
Lemma lem3206453 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term82 _83983 a s P) = (term83 _83983 a s P).
Proof. exact (MK_COMB (@lem3206452 _83983 a s P) (@lem3206450 _83983 a s P)). Qed.
Lemma lem3206454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3206455 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term84 _83983 a s P) = (term85 _83983 a s P).
Proof. exact (MK_COMB (@lem3206454) (@lem3206413 _83983 a s P)). Qed.
Lemma lem3206456 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term86 _83983 a s P) = (term87 _83983 a s P).
Proof. exact (MK_COMB (@lem3206455 _83983 a s P) (@lem3206447 _83983 a s P)). Qed.
Lemma lem3206457 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3206458 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term88 _83983 a s P) = (term89 _83983 a s P).
Proof. exact (MK_COMB (@lem3206457) (@lem3206456 _83983 a s P)). Qed.
Lemma lem3206459 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term90 _83983 a s P) = (term91 _83983 a s P).
Proof. exact (MK_COMB (@lem3206458 _83983 a s P) (@lem3206453 _83983 a s P)). Qed.
Lemma lem3206460 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term43 _83983 a s P) = (term90 _83983 a s P).
Proof. exact (@lem17646 (term14 _83983 a s P) (term17 _83983 a s P)). Qed.
Lemma lem3206461 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term43 _83983 a s P) = (term91 _83983 a s P).
Proof. exact (TRANS (@lem3206460 _83983 a s P) (@lem3206459 _83983 a s P)). Qed.
Lemma lem3206624 {A : Type'} (P : Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3206625 {_83983 : Type'} (P : Prop) (Q : _83983 -> Prop) : (term92 _83983 P Q) = (term93 _83983 P Q).
Proof. exact (@lem3206624 _83983 P Q). Qed.
Lemma lem3206626 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term94 _83983 a s P) = (term95 _83983 a s P).
Proof. exact (@lem3206625 _83983 (term96 _83983 P a) (term71 _83983 s P)). Qed.
Lemma lem3206627 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term97 _83983 s P x) = (term64 _83983 s P x).
Proof. exact (eq_refl (term97 _83983 s P x)). Qed.
Lemma lem3206628 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term98 _83983 s P) = (term71 _83983 s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206627 _83983 s P x)). Qed.
Lemma lem3206629 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206630 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term99 _83983 s P) = (term72 _83983 s P).
Proof. exact (MK_COMB (@lem3206629 _83983) (@lem3206628 _83983 s P)). Qed.
Lemma lem3206631 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term75 _83983 P a) = (term75 _83983 P a).
Proof. exact (eq_refl (term75 _83983 P a)). Qed.
Lemma lem3206632 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term94 _83983 a s P) = (term77 _83983 a s P).
Proof. exact (MK_COMB (@lem3206631 _83983 P a) (@lem3206630 _83983 s P)). Qed.
Lemma lem3206633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3206634 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term100 _83983 a s P) = (term101 _83983 a s P).
Proof. exact (MK_COMB (@lem3206633) (@lem3206632 _83983 a s P)). Qed.
Lemma lem3206635 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term97 _83983 s P x) = (term64 _83983 s P x).
Proof. exact (eq_refl (term97 _83983 s P x)). Qed.
Lemma lem3206636 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term75 _83983 P a) = (term75 _83983 P a).
Proof. exact (eq_refl (term75 _83983 P a)). Qed.
Lemma lem3206637 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term102 _83983 a s P x) = (term103 _83983 a s P x).
Proof. exact (MK_COMB (@lem3206636 _83983 P a) (@lem3206635 _83983 s P x)). Qed.
Lemma lem3206638 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term104 _83983 a s P) = (term105 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206637 _83983 a s P x)). Qed.
Lemma lem3206639 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206640 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term95 _83983 a s P) = (term106 _83983 a s P).
Proof. exact (MK_COMB (@lem3206639 _83983) (@lem3206638 _83983 a s P)). Qed.
Lemma lem3206641 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : ((term94 _83983 a s P) = (term95 _83983 a s P)) = ((term77 _83983 a s P) = (term106 _83983 a s P)).
Proof. exact (MK_COMB (@lem3206634 _83983 a s P) (@lem3206640 _83983 a s P)). Qed.
Lemma lem3206642 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term77 _83983 a s P) = (term106 _83983 a s P).
Proof. exact (EQ_MP (@lem3206641 _83983 a s P) (@lem3206626 _83983 a s P)). Qed.
Lemma lem3206643 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term85 _83983 a s P) = (term85 _83983 a s P).
Proof. exact (eq_refl (term85 _83983 a s P)). Qed.
Lemma lem3206644 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term87 _83983 a s P) = (term107 _83983 a s P).
Proof. exact (MK_COMB (@lem3206643 _83983 a s P) (@lem3206642 _83983 a s P)). Qed.
Lemma lem3206646 {A : Type'} (P : Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3206647 {_83983 : Type'} (P : Prop) (Q : _83983 -> Prop) : (term108 _83983 P Q) = (term109 _83983 P Q).
Proof. exact (@lem3206646 _83983 P Q). Qed.
Lemma lem3206648 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term110 _83983 a s P) = (term111 _83983 a s P).
Proof. exact (@lem3206647 _83983 (term62 _83983 a s P) (term105 _83983 a s P)). Qed.
Lemma lem3206649 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term112 _83983 a s P x) = (term103 _83983 a s P x).
Proof. exact (eq_refl (term112 _83983 a s P x)). Qed.
Lemma lem3206650 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term113 _83983 a s P) = (term105 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206649 _83983 a s P x)). Qed.
Lemma lem3206651 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206652 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term114 _83983 a s P) = (term106 _83983 a s P).
Proof. exact (MK_COMB (@lem3206651 _83983) (@lem3206650 _83983 a s P)). Qed.
Lemma lem3206653 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term85 _83983 a s P) = (term85 _83983 a s P).
Proof. exact (eq_refl (term85 _83983 a s P)). Qed.
Lemma lem3206654 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term110 _83983 a s P) = (term107 _83983 a s P).
Proof. exact (MK_COMB (@lem3206653 _83983 a s P) (@lem3206652 _83983 a s P)). Qed.
Lemma lem3206655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3206656 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term115 _83983 a s P) = (term116 _83983 a s P).
Proof. exact (MK_COMB (@lem3206655) (@lem3206654 _83983 a s P)). Qed.
Lemma lem3206657 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term112 _83983 a s P x) = (term103 _83983 a s P x).
Proof. exact (eq_refl (term112 _83983 a s P x)). Qed.
Lemma lem3206658 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term85 _83983 a s P) = (term85 _83983 a s P).
Proof. exact (eq_refl (term85 _83983 a s P)). Qed.
Lemma lem3206659 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term117 _83983 a s P x) = (term118 _83983 a s P x).
Proof. exact (MK_COMB (@lem3206658 _83983 a s P) (@lem3206657 _83983 a s P x)). Qed.
Lemma lem3206660 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term119 _83983 a s P) = (term120 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206659 _83983 a s P x)). Qed.
Lemma lem3206661 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206662 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term111 _83983 a s P) = (term121 _83983 a s P).
Proof. exact (MK_COMB (@lem3206661 _83983) (@lem3206660 _83983 a s P)). Qed.
Lemma lem3206663 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : ((term110 _83983 a s P) = (term111 _83983 a s P)) = ((term107 _83983 a s P) = (term121 _83983 a s P)).
Proof. exact (MK_COMB (@lem3206656 _83983 a s P) (@lem3206662 _83983 a s P)). Qed.
Lemma lem3206664 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term107 _83983 a s P) = (term121 _83983 a s P).
Proof. exact (EQ_MP (@lem3206663 _83983 a s P) (@lem3206648 _83983 a s P)). Qed.
Lemma lem3206665 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term87 _83983 a s P) = (term121 _83983 a s P).
Proof. exact (TRANS (@lem3206644 _83983 a s P) (@lem3206664 _83983 a s P)). Qed.
Lemma lem3206666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3206667 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term89 _83983 a s P) = (term122 _83983 a s P).
Proof. exact (MK_COMB (@lem3206666) (@lem3206665 _83983 a s P)). Qed.
Lemma lem3206669 {A : Type'} (P : A -> Prop) (Q : Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3206670 {_83983 : Type'} (P : _83983 -> Prop) (Q : Prop) : (term123 _83983 P Q) = (term124 _83983 P Q).
Proof. exact (@lem3206669 _83983 P Q). Qed.
Lemma lem3206671 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term125 _83983 a s P) = (term126 _83983 a s P).
Proof. exact (@lem3206670 _83983 (term59 _83983 a s P) (term79 _83983 a s P)). Qed.
Lemma lem3206672 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term127 _83983 a s P x) = (term47 _83983 a s P x).
Proof. exact (eq_refl (term127 _83983 a s P x)). Qed.
Lemma lem3206673 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term128 _83983 a s P) = (term59 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206672 _83983 a s P x)). Qed.
Lemma lem3206674 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206675 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term129 _83983 a s P) = (term60 _83983 a s P).
Proof. exact (MK_COMB (@lem3206674 _83983) (@lem3206673 _83983 a s P)). Qed.
Lemma lem3206676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3206677 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term130 _83983 a s P) = (term81 _83983 a s P).
Proof. exact (MK_COMB (@lem3206676) (@lem3206675 _83983 a s P)). Qed.
Lemma lem3206678 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term79 _83983 a s P) = (term79 _83983 a s P).
Proof. exact (eq_refl (term79 _83983 a s P)). Qed.
Lemma lem3206679 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term125 _83983 a s P) = (term83 _83983 a s P).
Proof. exact (MK_COMB (@lem3206677 _83983 a s P) (@lem3206678 _83983 a s P)). Qed.
Lemma lem3206680 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3206681 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term131 _83983 a s P) = (term132 _83983 a s P).
Proof. exact (MK_COMB (@lem3206680) (@lem3206679 _83983 a s P)). Qed.
Lemma lem3206682 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term127 _83983 a s P x) = (term47 _83983 a s P x).
Proof. exact (eq_refl (term127 _83983 a s P x)). Qed.
Lemma lem3206683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3206684 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term133 _83983 a s P x) = (term134 _83983 a s P x).
Proof. exact (MK_COMB (@lem3206683) (@lem3206682 _83983 a s P x)). Qed.
Lemma lem3206685 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term79 _83983 a s P) = (term79 _83983 a s P).
Proof. exact (eq_refl (term79 _83983 a s P)). Qed.
Lemma lem3206686 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term135 _83983 x a s P) = (term136 _83983 x a s P).
Proof. exact (MK_COMB (@lem3206684 _83983 a s P x) (@lem3206685 _83983 a s P)). Qed.
Lemma lem3206687 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term137 _83983 a s P) = (term138 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206686 _83983 x a s P)). Qed.
Lemma lem3206688 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206689 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term126 _83983 a s P) = (term139 _83983 a s P).
Proof. exact (MK_COMB (@lem3206688 _83983) (@lem3206687 _83983 a s P)). Qed.
Lemma lem3206690 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : ((term125 _83983 a s P) = (term126 _83983 a s P)) = ((term83 _83983 a s P) = (term139 _83983 a s P)).
Proof. exact (MK_COMB (@lem3206681 _83983 a s P) (@lem3206689 _83983 a s P)). Qed.
Lemma lem3206691 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term83 _83983 a s P) = (term139 _83983 a s P).
Proof. exact (EQ_MP (@lem3206690 _83983 a s P) (@lem3206671 _83983 a s P)). Qed.
Lemma lem3206692 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term91 _83983 a s P) = (term140 _83983 a s P).
Proof. exact (MK_COMB (@lem3206667 _83983 a s P) (@lem3206691 _83983 a s P)). Qed.
Lemma lem3206694 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3206695 {_83983 : Type'} (P : _83983 -> Prop) (Q : _83983 -> Prop) : (term141 _83983 P Q) = (term142 _83983 P Q).
Proof. exact (@lem3206694 _83983 P Q). Qed.
Lemma lem3206696 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term143 _83983 a s P) = (term144 _83983 a s P).
Proof. exact (@lem3206695 _83983 (term120 _83983 a s P) (term138 _83983 a s P)). Qed.
Lemma lem3206697 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term145 _83983 a s P x) = (term118 _83983 a s P x).
Proof. exact (eq_refl (term145 _83983 a s P x)). Qed.
Lemma lem3206698 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term146 _83983 a s P) = (term120 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206697 _83983 a s P x)). Qed.
Lemma lem3206699 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206700 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term147 _83983 a s P) = (term121 _83983 a s P).
Proof. exact (MK_COMB (@lem3206699 _83983) (@lem3206698 _83983 a s P)). Qed.
Lemma lem3206701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3206702 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term148 _83983 a s P) = (term122 _83983 a s P).
Proof. exact (MK_COMB (@lem3206701) (@lem3206700 _83983 a s P)). Qed.
Lemma lem3206703 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term149 _83983 a s P x) = (term136 _83983 x a s P).
Proof. exact (eq_refl (term149 _83983 a s P x)). Qed.
Lemma lem3206704 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term150 _83983 a s P) = (term138 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206703 _83983 x a s P)). Qed.
Lemma lem3206705 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206706 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term151 _83983 a s P) = (term139 _83983 a s P).
Proof. exact (MK_COMB (@lem3206705 _83983) (@lem3206704 _83983 a s P)). Qed.
Lemma lem3206707 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term143 _83983 a s P) = (term140 _83983 a s P).
Proof. exact (MK_COMB (@lem3206702 _83983 a s P) (@lem3206706 _83983 a s P)). Qed.
Lemma lem3206708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3206709 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term152 _83983 a s P) = (term153 _83983 a s P).
Proof. exact (MK_COMB (@lem3206708) (@lem3206707 _83983 a s P)). Qed.
Lemma lem3206710 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term145 _83983 a s P x) = (term118 _83983 a s P x).
Proof. exact (eq_refl (term145 _83983 a s P x)). Qed.
Lemma lem3206711 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3206712 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term154 _83983 a s P x) = (term155 _83983 a s P x).
Proof. exact (MK_COMB (@lem3206711) (@lem3206710 _83983 a s P x)). Qed.
Lemma lem3206713 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term149 _83983 a s P x) = (term136 _83983 x a s P).
Proof. exact (eq_refl (term149 _83983 a s P x)). Qed.
Lemma lem3206714 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term156 _83983 a s P x) = (term157 _83983 x a s P).
Proof. exact (MK_COMB (@lem3206712 _83983 a s P x) (@lem3206713 _83983 x a s P)). Qed.
Lemma lem3206715 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term158 _83983 a s P) = (term159 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206714 _83983 x a s P)). Qed.
Lemma lem3206716 {_83983 : Type'} : (@ex _83983) = (@ex _83983).
Proof. exact (eq_refl (@ex _83983)). Qed.
Lemma lem3206717 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term144 _83983 a s P) = (term160 _83983 a s P).
Proof. exact (MK_COMB (@lem3206716 _83983) (@lem3206715 _83983 a s P)). Qed.
Lemma lem3206718 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : ((term143 _83983 a s P) = (term144 _83983 a s P)) = ((term140 _83983 a s P) = (term160 _83983 a s P)).
Proof. exact (MK_COMB (@lem3206709 _83983 a s P) (@lem3206717 _83983 a s P)). Qed.
Lemma lem3206719 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term140 _83983 a s P) = (term160 _83983 a s P).
Proof. exact (EQ_MP (@lem3206718 _83983 a s P) (@lem3206696 _83983 a s P)). Qed.
Lemma lem3206721 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term91 _83983 a s P) = (term160 _83983 a s P).
Proof. exact (TRANS (@lem3206692 _83983 a s P) (@lem3206719 _83983 a s P)). Qed.
Lemma lem3206722 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term43 _83983 a s P) = (term160 _83983 a s P).
Proof. exact (TRANS (@lem3206461 _83983 a s P) (@lem3206721 _83983 a s P)). Qed.
Lemma lem3206723 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term43 _83983 a s P) : term160 _83983 a s P.
Proof. exact (EQ_MP (@lem3206722 _83983 a s P) (@lem3206376 _83983 a s P h1)). Qed.
Lemma lem3206724 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term157 _83983 x a s P) : term157 _83983 x a s P.
Proof. exact (h1). Qed.
Lemma lem3206737 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term65 _83983 s P x) = (term65 _83983 s P x).
Proof. exact (eq_refl (term65 _83983 s P x)). Qed.
Lemma lem3206738 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term73 _83983 s P) = (term73 _83983 s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206737 _83983 s P x)). Qed.
Lemma lem3206739 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206740 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term74 _83983 s P) = (term74 _83983 s P).
Proof. exact (MK_COMB (@lem3206739 _83983) (@lem3206738 _83983 s P)). Qed.
Lemma lem3206745 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term41 _83983 P a) = (term41 _83983 P a).
Proof. exact (eq_refl (term41 _83983 P a)). Qed.
Lemma lem3206746 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term79 _83983 a s P) = (term79 _83983 a s P).
Proof. exact (MK_COMB (@lem3206745 _83983 P a) (@lem3206740 _83983 s P)). Qed.
Lemma lem3206769 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term134 _83983 a s P x) = (term134 _83983 a s P x).
Proof. exact (eq_refl (term134 _83983 a s P x)). Qed.
Lemma lem3206770 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term136 _83983 x a s P) = (term136 _83983 x a s P).
Proof. exact (MK_COMB (@lem3206769 _83983 a s P x) (@lem3206746 _83983 a s P)). Qed.
Lemma lem3206791 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term103 _83983 a s P x) = (term103 _83983 a s P x).
Proof. exact (eq_refl (term103 _83983 a s P x)). Qed.
Lemma lem3206814 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term51 _83983 a s P x) = (term51 _83983 a s P x).
Proof. exact (eq_refl (term51 _83983 a s P x)). Qed.
Lemma lem3206815 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term61 _83983 a s P) = (term61 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206814 _83983 a s P x)). Qed.
Lemma lem3206816 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206817 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term62 _83983 a s P) = (term62 _83983 a s P).
Proof. exact (MK_COMB (@lem3206816 _83983) (@lem3206815 _83983 a s P)). Qed.
Lemma lem3206818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3206819 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term85 _83983 a s P) = (term85 _83983 a s P).
Proof. exact (MK_COMB (@lem3206818) (@lem3206817 _83983 a s P)). Qed.
Lemma lem3206820 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term118 _83983 a s P x) = (term118 _83983 a s P x).
Proof. exact (MK_COMB (@lem3206819 _83983 a s P) (@lem3206791 _83983 a s P x)). Qed.
Lemma lem3206821 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3206822 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term155 _83983 a s P x) = (term155 _83983 a s P x).
Proof. exact (MK_COMB (@lem3206821) (@lem3206820 _83983 a s P x)). Qed.
Lemma lem3206823 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term157 _83983 x a s P) = (term157 _83983 x a s P).
Proof. exact (MK_COMB (@lem3206822 _83983 a s P x) (@lem3206770 _83983 x a s P)). Qed.
Lemma lem3206824 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term157 _83983 x a s P) : term157 _83983 x a s P.
Proof. exact (EQ_MP (@lem3206823 _83983 x a s P) (@lem3206724 _83983 x a s P h1)). Qed.
Lemma lem3206825 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term118 _83983 a s P x.
Proof. exact (h1). Qed.
Lemma lem3206826 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term136 _83983 x a s P.
Proof. exact (h1). Qed.
Lemma lem3206827 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term103 _83983 a s P x.
Proof. exact (proj2 (@lem3206825 _83983 a s P x h1)). Qed.
Lemma lem3206828 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term62 _83983 a s P.
Proof. exact (proj1 (@lem3206825 _83983 a s P x h1)). Qed.
Lemma lem3206830 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term64 _83983 s P x) : term64 _83983 s P x.
Proof. exact (h1). Qed.
Lemma lem3206833 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term79 _83983 a s P.
Proof. exact (proj2 (@lem3206826 _83983 x a s P h1)). Qed.
Lemma lem3206834 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term47 _83983 a s P x.
Proof. exact (proj1 (@lem3206826 _83983 x a s P h1)). Qed.
Lemma lem3206835 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term74 _83983 s P.
Proof. exact (proj2 (@lem3206833 _83983 x a s P h1)). Qed.
Lemma lem3206838 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term6 _83983 a x s.
Proof. exact (proj1 (@lem3206834 _83983 x a s P h1)). Qed.
Lemma lem3206858 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term51 _83983 a s P x) = (term161 _83983 a s P x).
Proof. exact (@lem19699 (term162 _83983 x a) (term163 _83983 x s) (P x)). Qed.
Lemma lem3206859 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term61 _83983 a s P) = (term164 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206858 _83983 a s P x)). Qed.
Lemma lem3206860 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206862 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term62 _83983 a s P) = (term165 _83983 a s P).
Proof. exact (MK_COMB (@lem3206860 _83983) (@lem3206859 _83983 a s P)). Qed.
Lemma lem3206863 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term165 _83983 a s P.
Proof. exact (EQ_MP (@lem3206862 _83983 a s P) (@lem3206828 _83983 a s P x h1)). Qed.
Lemma lem3206867 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) (h1 : term96 _83983 P a) : term96 _83983 P a.
Proof. exact (h1). Qed.
Lemma lem3206885 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term51 _83983 a s P x) = (term161 _83983 a s P x).
Proof. exact (@lem19699 (term162 _83983 x a) (term163 _83983 x s) (P x)). Qed.
Lemma lem3206886 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term61 _83983 a s P) = (term164 _83983 a s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206885 _83983 a s P x)). Qed.
Lemma lem3206887 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206889 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term62 _83983 a s P) = (term165 _83983 a s P).
Proof. exact (MK_COMB (@lem3206887 _83983) (@lem3206886 _83983 a s P)). Qed.
Lemma lem3206890 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term165 _83983 a s P.
Proof. exact (EQ_MP (@lem3206889 _83983 a s P) (@lem3206828 _83983 a s P x h1)). Qed.
Lemma lem3206923 {_83983 : Type'} (x : _83983) (a : _83983) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3206935 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) : (term65 _83983 s P x) = (term65 _83983 s P x).
Proof. exact (eq_refl (term65 _83983 s P x)). Qed.
Lemma lem3206936 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term73 _83983 s P) = (term73 _83983 s P).
Proof. exact (fun_ext (fun x : _83983 => @lem3206935 _83983 s P x)). Qed.
Lemma lem3206937 {_83983 : Type'} : (@all _83983) = (@all _83983).
Proof. exact (eq_refl (@all _83983)). Qed.
Lemma lem3206939 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) : (term74 _83983 s P) = (term74 _83983 s P).
Proof. exact (MK_COMB (@lem3206937 _83983) (@lem3206936 _83983 s P)). Qed.
Lemma lem3206940 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term74 _83983 s P.
Proof. exact (EQ_MP (@lem3206939 _83983 s P) (@lem3206835 _83983 x a s P h1)). Qed.
Lemma lem3206948 {_83983 : Type'} (x : _83983) (s : _83983 -> Prop) (h1 : @IN _83983 x s) : @IN _83983 x s.
Proof. exact (h1). Qed.
Lemma lem3206949 {_83983 : Type'} (_32948 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term166 _83983 a s P _32948.
Proof. exact (@lem3206863 _83983 a s P x h1 _32948). Qed.
Lemma lem3206950 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (_32948 : _83983) : (term166 _83983 a s P _32948) = (term161 _83983 a s P _32948).
Proof. exact (eq_refl (term166 _83983 a s P _32948)). Qed.
Lemma lem3206951 {_83983 : Type'} (_32948 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term161 _83983 a s P _32948.
Proof. exact (EQ_MP (@lem3206950 _83983 a s P _32948) (@lem3206949 _83983 _32948 a s P x h1)). Qed.
Lemma lem3206952 {_83983 : Type'} (_32949 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term166 _83983 a s P _32949.
Proof. exact (@lem3206890 _83983 a s P x h1 _32949). Qed.
Lemma lem3206953 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (_32949 : _83983) : (term166 _83983 a s P _32949) = (term161 _83983 a s P _32949).
Proof. exact (eq_refl (term166 _83983 a s P _32949)). Qed.
Lemma lem3206954 {_83983 : Type'} (_32949 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term161 _83983 a s P _32949.
Proof. exact (EQ_MP (@lem3206953 _83983 a s P _32949) (@lem3206952 _83983 _32949 a s P x h1)). Qed.
Lemma lem3206958 {_83983 : Type'} (_32951 : _83983) (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term167 _83983 s P _32951.
Proof. exact (@lem3206940 _83983 x a s P h1 _32951). Qed.
Lemma lem3206959 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (_32951 : _83983) : (term167 _83983 s P _32951) = (term65 _83983 s P _32951).
Proof. exact (eq_refl (term167 _83983 s P _32951)). Qed.
Lemma lem3206966 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) (h1 : term96 _83983 P a) : term96 _83983 P a.
Proof. exact (h1). Qed.
Lemma lem3206972 {_83983 : Type'} (_32948 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term168 _83983 a P _32948.
Proof. exact (proj1 (@lem3206951 _83983 _32948 a s P x h1)). Qed.
Lemma lem3206982 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term64 _83983 s P x) : term96 _83983 P x.
Proof. exact (proj2 (@lem3206830 _83983 s P x h1)). Qed.
Lemma lem3206994 {_83983 : Type'} (_32949 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term65 _83983 s P _32949.
Proof. exact (proj2 (@lem3206954 _83983 _32949 a s P x h1)). Qed.
Lemma lem3207004 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term96 _83983 P x.
Proof. exact (proj2 (@lem3206834 _83983 x a s P h1)). Qed.
Lemma lem3207006 {_83983 : Type'} (x : _83983) (a : _83983) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3207014 {_83983 : Type'} (_32951 : _83983) (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term65 _83983 s P _32951.
Proof. exact (EQ_MP (@lem3206959 _83983 s P _32951) (@lem3206958 _83983 _32951 x a s P h1)). Qed.
Lemma lem3207016 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term96 _83983 P x.
Proof. exact (proj2 (@lem3206834 _83983 x a s P h1)). Qed.
Lemma lem3207018 {_83983 : Type'} (x : _83983) (s : _83983 -> Prop) (h1 : @IN _83983 x s) : @IN _83983 x s.
Proof. exact (h1). Qed.
Lemma lem3207061 {_83983 : Type'} (P : _83983 -> Prop) : (term169 _83983 P) = (term169 _83983 P).
Proof. exact (eq_refl (term169 _83983 P)). Qed.
Lemma lem3207062 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : x = a) : (term170 _83983 P x) = (term170 _83983 P a).
Proof. exact (MK_COMB (@lem3207061 _83983 P) (@lem3207006 _83983 x a h1)). Qed.
Lemma lem3207063 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term170 _83983 P a) = (term96 _83983 P a).
Proof. exact (eq_refl (term170 _83983 P a)). Qed.
Lemma lem3207064 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) : (term171 _83983 P x) = (term171 _83983 P x).
Proof. exact (eq_refl (term171 _83983 P x)). Qed.
Lemma lem3207065 {_83983 : Type'} (x : _83983) (P : _83983 -> Prop) (a : _83983) : ((term170 _83983 P x) = (term170 _83983 P a)) = ((term170 _83983 P x) = (term96 _83983 P a)).
Proof. exact (MK_COMB (@lem3207064 _83983 P x) (@lem3207063 _83983 P a)). Qed.
Lemma lem3207066 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) : (term170 _83983 P x) = (term96 _83983 P x).
Proof. exact (eq_refl (term170 _83983 P x)). Qed.
Lemma lem3207067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3207068 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) : (term171 _83983 P x) = (term172 _83983 P x).
Proof. exact (MK_COMB (@lem3207067) (@lem3207066 _83983 P x)). Qed.
Lemma lem3207069 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term96 _83983 P a) = (term96 _83983 P a).
Proof. exact (eq_refl (term96 _83983 P a)). Qed.
Lemma lem3207070 {_83983 : Type'} (x : _83983) (P : _83983 -> Prop) (a : _83983) : ((term170 _83983 P x) = (term96 _83983 P a)) = ((term96 _83983 P x) = (term96 _83983 P a)).
Proof. exact (MK_COMB (@lem3207068 _83983 P x) (@lem3207069 _83983 P a)). Qed.
Lemma lem3207071 {_83983 : Type'} (x : _83983) (P : _83983 -> Prop) (a : _83983) : ((term170 _83983 P x) = (term170 _83983 P a)) = ((term96 _83983 P x) = (term96 _83983 P a)).
Proof. exact (TRANS (@lem3207065 _83983 x P a) (@lem3207070 _83983 x P a)). Qed.
Lemma lem3207072 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : x = a) : (term96 _83983 P x) = (term96 _83983 P a).
Proof. exact (EQ_MP (@lem3207071 _83983 x P a) (@lem3207062 _83983 P x a h1)). Qed.
Lemma lem3207073 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : term96 _83983 P a.
Proof. exact (EQ_MP (@lem3207072 _83983 P x a h2) (@lem3207004 _83983 x a s P h1)). Qed.
Lemma lem3207110 {_83983 : Type'} (x : _83983) : x = x.
Proof. exact (@lem21386 _83983 x). Qed.
Lemma lem3207111 {_83983 : Type'} (x : _83983) : x = x.
Proof. exact (@lem3207110 _83983 x). Qed.
Lemma lem3207112 {_83983 : Type'} (a : _83983) : a = a.
Proof. exact (@lem3207111 _83983 a). Qed.
Lemma lem3207113 {_83983 : Type'} (a : _83983) : term173 _83983 a.
Proof. exact (fun h0 : term174 _83983 a => @lem3207112 _83983 a). Qed.
Lemma lem3207115 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207116 {_83983 : Type'} (a : _83983) : (term173 _83983 a) = (a = a).
Proof. exact (@lem3207115 (a = a)). Qed.
Lemma lem3207117 {_83983 : Type'} (a : _83983) : a = a.
Proof. exact (EQ_MP (@lem3207116 _83983 a) (@lem3207113 _83983 a)). Qed.
Lemma lem3207123 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3207124 {_83983 : Type'} (P : _83983 -> Prop) (_32948 : _83983) (a : _83983) : (term168 _83983 a P _32948) = (term176 _83983 P _32948 a).
Proof. exact (@lem3207123 (P _32948) (term162 _83983 _32948 a)). Qed.
Lemma lem3207132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3207133 {_83983 : Type'} (P : _83983 -> Prop) (_32948 : _83983) (a : _83983) : (term177 _83983 a P _32948) = (term178 _83983 P _32948 a).
Proof. exact (MK_COMB (@lem3207132) (@lem3207124 _83983 P _32948 a)). Qed.
Lemma lem3207141 {_83983 : Type'} (P : _83983 -> Prop) (_32948 : _83983) (a : _83983) : (term176 _83983 P _32948 a) = (term176 _83983 P _32948 a).
Proof. exact (eq_refl (term176 _83983 P _32948 a)). Qed.
Lemma lem3207142 {_83983 : Type'} (P : _83983 -> Prop) (_32948 : _83983) (a : _83983) : ((term168 _83983 a P _32948) = (term176 _83983 P _32948 a)) = ((term176 _83983 P _32948 a) = (term176 _83983 P _32948 a)).
Proof. exact (MK_COMB (@lem3207133 _83983 P _32948 a) (@lem3207141 _83983 P _32948 a)). Qed.
Lemma lem3207144 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3207145 (x : Prop) : (x = x) = True.
Proof. exact (@lem3207144 Prop x). Qed.
Lemma lem3207146 {_83983 : Type'} (P : _83983 -> Prop) (_32948 : _83983) (a : _83983) : ((term176 _83983 P _32948 a) = (term176 _83983 P _32948 a)) = True.
Proof. exact (@lem3207145 (term176 _83983 P _32948 a)). Qed.
Lemma lem3207147 {_83983 : Type'} (P : _83983 -> Prop) (_32948 : _83983) (a : _83983) : ((term168 _83983 a P _32948) = (term176 _83983 P _32948 a)) = True.
Proof. exact (TRANS (@lem3207142 _83983 P _32948 a) (@lem3207146 _83983 P _32948 a)). Qed.
Lemma lem3207148 {_83983 : Type'} (P : _83983 -> Prop) (_32948 : _83983) (a : _83983) : True = ((term168 _83983 a P _32948) = (term176 _83983 P _32948 a)).
Proof. exact (SYM (@lem3207147 _83983 P _32948 a)). Qed.
Lemma lem3207149 {_83983 : Type'} (P : _83983 -> Prop) (_32948 : _83983) (a : _83983) : (term168 _83983 a P _32948) = (term176 _83983 P _32948 a).
Proof. exact (EQ_MP (@lem3207148 _83983 P _32948 a) (@lem0)). Qed.
Lemma lem3207150 {_83983 : Type'} (_32948 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term176 _83983 P _32948 a.
Proof. exact (EQ_MP (@lem3207149 _83983 P _32948 a) (@lem3206972 _83983 _32948 a s P x h1)). Qed.
Lemma lem3207152 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3207153 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (_32948 : _83983) : (term176 _83983 P _32948 a) = (term180 _83983 a P _32948).
Proof. exact (@lem3207152 (term162 _83983 _32948 a) (P _32948)). Qed.
Lemma lem3207155 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3207156 {_83983 : Type'} (_32948 : _83983) (a : _83983) : (term181 _83983 _32948 a) = (_32948 = a).
Proof. exact (@lem3207155 (_32948 = a)). Qed.
Lemma lem3207157 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3207158 {_83983 : Type'} (_32948 : _83983) (a : _83983) : (term182 _83983 _32948 a) = (term183 _83983 _32948 a).
Proof. exact (MK_COMB (@lem3207157) (@lem3207156 _83983 _32948 a)). Qed.
Lemma lem3207159 {_83983 : Type'} (P : _83983 -> Prop) (_32948 : _83983) : (P _32948) = (P _32948).
Proof. exact (eq_refl (P _32948)). Qed.
Lemma lem3207160 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (_32948 : _83983) : (term180 _83983 a P _32948) = (term184 _83983 a P _32948).
Proof. exact (MK_COMB (@lem3207158 _83983 _32948 a) (@lem3207159 _83983 P _32948)). Qed.
Lemma lem3207161 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (_32948 : _83983) : (term176 _83983 P _32948 a) = (term184 _83983 a P _32948).
Proof. exact (TRANS (@lem3207153 _83983 a P _32948) (@lem3207160 _83983 a P _32948)). Qed.
Lemma lem3207164 {_83983 : Type'} (_32948 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term184 _83983 a P _32948.
Proof. exact (EQ_MP (@lem3207161 _83983 a P _32948) (@lem3207150 _83983 _32948 a s P x h1)). Qed.
Lemma lem3207165 {_83983 : Type'} (_32948 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term184 _83983 a P _32948.
Proof. exact (@lem3207164 _83983 _32948 a s P x h1). Qed.
Lemma lem3207166 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term185 _83983 P a.
Proof. exact (@lem3207165 _83983 a a s P x h1). Qed.
Lemma lem3207169 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : P a.
Proof. exact (@lem3207166 _83983 a s P x h1 (@lem3207117 _83983 a)). Qed.
Lemma lem3207170 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term186 _83983 P a.
Proof. exact (fun h0 : term96 _83983 P a => @lem3207169 _83983 a s P x h1). Qed.
Lemma lem3207172 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207173 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term186 _83983 P a) = (P a).
Proof. exact (@lem3207172 (P a)). Qed.
Lemma lem3207174 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : P a.
Proof. exact (EQ_MP (@lem3207173 _83983 P a) (@lem3207170 _83983 a s P x h1)). Qed.
Lemma lem3207177 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3207179 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term96 _83983 P a) = (term187 _83983 P a).
Proof. exact (@lem3207177 (P a)). Qed.
Lemma lem3207182 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) (h1 : term96 _83983 P a) : term187 _83983 P a.
Proof. exact (EQ_MP (@lem3207179 _83983 P a) (@lem3206966 _83983 P a h1)). Qed.
Lemma lem3207185 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term96 _83983 P a) (h2 : term118 _83983 a s P x) : False.
Proof. exact (@lem3207182 _83983 P a h1 (@lem3207174 _83983 a s P x h2)). Qed.
Lemma lem3207186 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term96 _83983 P a) (h2 : term118 _83983 a s P x) : term188.
Proof. exact (fun h0 : ~ False => @lem3207185 _83983 a s P x h1 h2). Qed.
Lemma lem3207188 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207189 : term188 = False.
Proof. exact (@lem3207188 False). Qed.
Lemma lem3207190 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term96 _83983 P a) (h2 : term118 _83983 a s P x) : False.
Proof. exact (EQ_MP (@lem3207189) (@lem3207186 _83983 a s P x h1 h2)). Qed.
Lemma lem3207227 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term64 _83983 s P x) : @IN _83983 x s.
Proof. exact (proj1 (@lem3206830 _83983 s P x h1)). Qed.
Lemma lem3207228 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term64 _83983 s P x) : term189 _83983 x s.
Proof. exact (fun h0 : term163 _83983 x s => @lem3207227 _83983 s P x h1). Qed.
Lemma lem3207230 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207231 {_83983 : Type'} (x : _83983) (s : _83983 -> Prop) : (term189 _83983 x s) = (@IN _83983 x s).
Proof. exact (@lem3207230 (@IN _83983 x s)). Qed.
Lemma lem3207232 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term64 _83983 s P x) : @IN _83983 x s.
Proof. exact (EQ_MP (@lem3207231 _83983 x s) (@lem3207228 _83983 s P x h1)). Qed.
Lemma lem3207238 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3207239 {_83983 : Type'} (P : _83983 -> Prop) (_32949 : _83983) (s : _83983 -> Prop) : (term65 _83983 s P _32949) = (term190 _83983 P _32949 s).
Proof. exact (@lem3207238 (P _32949) (term163 _83983 _32949 s)). Qed.
Lemma lem3207245 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3207246 {_83983 : Type'} (P : _83983 -> Prop) (_32949 : _83983) (s : _83983 -> Prop) : (term191 _83983 s P _32949) = (term192 _83983 P _32949 s).
Proof. exact (MK_COMB (@lem3207245) (@lem3207239 _83983 P _32949 s)). Qed.
Lemma lem3207252 {_83983 : Type'} (P : _83983 -> Prop) (_32949 : _83983) (s : _83983 -> Prop) : (term190 _83983 P _32949 s) = (term190 _83983 P _32949 s).
Proof. exact (eq_refl (term190 _83983 P _32949 s)). Qed.
Lemma lem3207253 {_83983 : Type'} (P : _83983 -> Prop) (_32949 : _83983) (s : _83983 -> Prop) : ((term65 _83983 s P _32949) = (term190 _83983 P _32949 s)) = ((term190 _83983 P _32949 s) = (term190 _83983 P _32949 s)).
Proof. exact (MK_COMB (@lem3207246 _83983 P _32949 s) (@lem3207252 _83983 P _32949 s)). Qed.
Lemma lem3207255 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3207256 (x : Prop) : (x = x) = True.
Proof. exact (@lem3207255 Prop x). Qed.
Lemma lem3207257 {_83983 : Type'} (P : _83983 -> Prop) (_32949 : _83983) (s : _83983 -> Prop) : ((term190 _83983 P _32949 s) = (term190 _83983 P _32949 s)) = True.
Proof. exact (@lem3207256 (term190 _83983 P _32949 s)). Qed.
Lemma lem3207258 {_83983 : Type'} (P : _83983 -> Prop) (_32949 : _83983) (s : _83983 -> Prop) : ((term65 _83983 s P _32949) = (term190 _83983 P _32949 s)) = True.
Proof. exact (TRANS (@lem3207253 _83983 P _32949 s) (@lem3207257 _83983 P _32949 s)). Qed.
Lemma lem3207259 {_83983 : Type'} (P : _83983 -> Prop) (_32949 : _83983) (s : _83983 -> Prop) : True = ((term65 _83983 s P _32949) = (term190 _83983 P _32949 s)).
Proof. exact (SYM (@lem3207258 _83983 P _32949 s)). Qed.
Lemma lem3207260 {_83983 : Type'} (P : _83983 -> Prop) (_32949 : _83983) (s : _83983 -> Prop) : (term65 _83983 s P _32949) = (term190 _83983 P _32949 s).
Proof. exact (EQ_MP (@lem3207259 _83983 P _32949 s) (@lem0)). Qed.
Lemma lem3207261 {_83983 : Type'} (_32949 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term190 _83983 P _32949 s.
Proof. exact (EQ_MP (@lem3207260 _83983 P _32949 s) (@lem3206994 _83983 _32949 a s P x h1)). Qed.
Lemma lem3207263 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3207264 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (_32949 : _83983) : (term190 _83983 P _32949 s) = (term193 _83983 s P _32949).
Proof. exact (@lem3207263 (term163 _83983 _32949 s) (P _32949)). Qed.
Lemma lem3207266 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3207267 {_83983 : Type'} (_32949 : _83983) (s : _83983 -> Prop) : (term194 _83983 _32949 s) = (@IN _83983 _32949 s).
Proof. exact (@lem3207266 (@IN _83983 _32949 s)). Qed.
Lemma lem3207268 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3207269 {_83983 : Type'} (_32949 : _83983) (s : _83983 -> Prop) : (term195 _83983 _32949 s) = (term196 _83983 _32949 s).
Proof. exact (MK_COMB (@lem3207268) (@lem3207267 _83983 _32949 s)). Qed.
Lemma lem3207270 {_83983 : Type'} (P : _83983 -> Prop) (_32949 : _83983) : (P _32949) = (P _32949).
Proof. exact (eq_refl (P _32949)). Qed.
Lemma lem3207271 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (_32949 : _83983) : (term193 _83983 s P _32949) = (term38 _83983 s P _32949).
Proof. exact (MK_COMB (@lem3207269 _83983 _32949 s) (@lem3207270 _83983 P _32949)). Qed.
Lemma lem3207272 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (_32949 : _83983) : (term190 _83983 P _32949 s) = (term38 _83983 s P _32949).
Proof. exact (TRANS (@lem3207264 _83983 s P _32949) (@lem3207271 _83983 s P _32949)). Qed.
Lemma lem3207275 {_83983 : Type'} (_32949 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term38 _83983 s P _32949.
Proof. exact (EQ_MP (@lem3207272 _83983 s P _32949) (@lem3207261 _83983 _32949 a s P x h1)). Qed.
Lemma lem3207276 {_83983 : Type'} (_32949 : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term38 _83983 s P _32949.
Proof. exact (@lem3207275 _83983 _32949 a s P x h1). Qed.
Lemma lem3207277 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : term38 _83983 s P x.
Proof. exact (@lem3207276 _83983 x a s P x h1). Qed.
Lemma lem3207280 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) (h2 : term64 _83983 s P x) : P x.
Proof. exact (@lem3207277 _83983 a s P x h1 (@lem3207232 _83983 s P x h2)). Qed.
Lemma lem3207281 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) (h2 : term64 _83983 s P x) : term186 _83983 P x.
Proof. exact (fun h0 : term96 _83983 P x => @lem3207280 _83983 a s P x h1 h2). Qed.
Lemma lem3207283 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207284 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) : (term186 _83983 P x) = (P x).
Proof. exact (@lem3207283 (P x)). Qed.
Lemma lem3207285 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) (h2 : term64 _83983 s P x) : P x.
Proof. exact (EQ_MP (@lem3207284 _83983 P x) (@lem3207281 _83983 a s P x h1 h2)). Qed.
Lemma lem3207288 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3207290 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) : (term96 _83983 P x) = (term187 _83983 P x).
Proof. exact (@lem3207288 (P x)). Qed.
Lemma lem3207293 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term64 _83983 s P x) : term187 _83983 P x.
Proof. exact (EQ_MP (@lem3207290 _83983 P x) (@lem3206982 _83983 s P x h1)). Qed.
Lemma lem3207296 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) (h2 : term64 _83983 s P x) : False.
Proof. exact (@lem3207293 _83983 s P x h2 (@lem3207285 _83983 a s P x h1 h2)). Qed.
Lemma lem3207297 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) (h2 : term64 _83983 s P x) : term188.
Proof. exact (fun h0 : ~ False => @lem3207296 _83983 a s P x h1 h2). Qed.
Lemma lem3207299 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207300 : term188 = False.
Proof. exact (@lem3207299 False). Qed.
Lemma lem3207301 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) (h2 : term64 _83983 s P x) : False.
Proof. exact (EQ_MP (@lem3207300) (@lem3207297 _83983 a s P x h1 h2)). Qed.
Lemma lem3207303 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : P a.
Proof. exact (proj1 (@lem3206833 _83983 x a s P h1)). Qed.
Lemma lem3207304 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term186 _83983 P a.
Proof. exact (fun h0 : term96 _83983 P a => @lem3207303 _83983 x a s P h1). Qed.
Lemma lem3207306 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207307 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term186 _83983 P a) = (P a).
Proof. exact (@lem3207306 (P a)). Qed.
Lemma lem3207308 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : P a.
Proof. exact (EQ_MP (@lem3207307 _83983 P a) (@lem3207304 _83983 x a s P h1)). Qed.
Lemma lem3207311 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3207313 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : (term96 _83983 P a) = (term187 _83983 P a).
Proof. exact (@lem3207311 (P a)). Qed.
Lemma lem3207316 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : term187 _83983 P a.
Proof. exact (EQ_MP (@lem3207313 _83983 P a) (@lem3207073 _83983 s P x a h1 h2)). Qed.
Lemma lem3207319 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : False.
Proof. exact (@lem3207316 _83983 s P x a h1 h2 (@lem3207308 _83983 x a s P h1)). Qed.
Lemma lem3207320 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : term188.
Proof. exact (fun h0 : ~ False => @lem3207319 _83983 s P x a h1 h2). Qed.
Lemma lem3207322 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207323 : term188 = False.
Proof. exact (@lem3207322 False). Qed.
Lemma lem3207326 {_83983 : Type'} (x : _83983) (s : _83983 -> Prop) (h1 : @IN _83983 x s) : @IN _83983 x s.
Proof. exact (h1). Qed.
Lemma lem3207327 {_83983 : Type'} (x : _83983) (s : _83983 -> Prop) (h1 : @IN _83983 x s) : term189 _83983 x s.
Proof. exact (fun h0 : term163 _83983 x s => @lem3207326 _83983 x s h1). Qed.
Lemma lem3207329 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207330 {_83983 : Type'} (x : _83983) (s : _83983 -> Prop) : (term189 _83983 x s) = (@IN _83983 x s).
Proof. exact (@lem3207329 (@IN _83983 x s)). Qed.
Lemma lem3207331 {_83983 : Type'} (x : _83983) (s : _83983 -> Prop) (h1 : @IN _83983 x s) : @IN _83983 x s.
Proof. exact (EQ_MP (@lem3207330 _83983 x s) (@lem3207327 _83983 x s h1)). Qed.
Lemma lem3207337 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3207338 {_83983 : Type'} (P : _83983 -> Prop) (_32951 : _83983) (s : _83983 -> Prop) : (term65 _83983 s P _32951) = (term190 _83983 P _32951 s).
Proof. exact (@lem3207337 (P _32951) (term163 _83983 _32951 s)). Qed.
Lemma lem3207344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3207345 {_83983 : Type'} (P : _83983 -> Prop) (_32951 : _83983) (s : _83983 -> Prop) : (term191 _83983 s P _32951) = (term192 _83983 P _32951 s).
Proof. exact (MK_COMB (@lem3207344) (@lem3207338 _83983 P _32951 s)). Qed.
Lemma lem3207351 {_83983 : Type'} (P : _83983 -> Prop) (_32951 : _83983) (s : _83983 -> Prop) : (term190 _83983 P _32951 s) = (term190 _83983 P _32951 s).
Proof. exact (eq_refl (term190 _83983 P _32951 s)). Qed.
Lemma lem3207352 {_83983 : Type'} (P : _83983 -> Prop) (_32951 : _83983) (s : _83983 -> Prop) : ((term65 _83983 s P _32951) = (term190 _83983 P _32951 s)) = ((term190 _83983 P _32951 s) = (term190 _83983 P _32951 s)).
Proof. exact (MK_COMB (@lem3207345 _83983 P _32951 s) (@lem3207351 _83983 P _32951 s)). Qed.
Lemma lem3207354 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3207355 (x : Prop) : (x = x) = True.
Proof. exact (@lem3207354 Prop x). Qed.
Lemma lem3207356 {_83983 : Type'} (P : _83983 -> Prop) (_32951 : _83983) (s : _83983 -> Prop) : ((term190 _83983 P _32951 s) = (term190 _83983 P _32951 s)) = True.
Proof. exact (@lem3207355 (term190 _83983 P _32951 s)). Qed.
Lemma lem3207357 {_83983 : Type'} (P : _83983 -> Prop) (_32951 : _83983) (s : _83983 -> Prop) : ((term65 _83983 s P _32951) = (term190 _83983 P _32951 s)) = True.
Proof. exact (TRANS (@lem3207352 _83983 P _32951 s) (@lem3207356 _83983 P _32951 s)). Qed.
Lemma lem3207358 {_83983 : Type'} (P : _83983 -> Prop) (_32951 : _83983) (s : _83983 -> Prop) : True = ((term65 _83983 s P _32951) = (term190 _83983 P _32951 s)).
Proof. exact (SYM (@lem3207357 _83983 P _32951 s)). Qed.
Lemma lem3207359 {_83983 : Type'} (P : _83983 -> Prop) (_32951 : _83983) (s : _83983 -> Prop) : (term65 _83983 s P _32951) = (term190 _83983 P _32951 s).
Proof. exact (EQ_MP (@lem3207358 _83983 P _32951 s) (@lem0)). Qed.
Lemma lem3207360 {_83983 : Type'} (_32951 : _83983) (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term190 _83983 P _32951 s.
Proof. exact (EQ_MP (@lem3207359 _83983 P _32951 s) (@lem3207014 _83983 _32951 x a s P h1)). Qed.
Lemma lem3207362 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3207363 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (_32951 : _83983) : (term190 _83983 P _32951 s) = (term193 _83983 s P _32951).
Proof. exact (@lem3207362 (term163 _83983 _32951 s) (P _32951)). Qed.
Lemma lem3207365 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3207366 {_83983 : Type'} (_32951 : _83983) (s : _83983 -> Prop) : (term194 _83983 _32951 s) = (@IN _83983 _32951 s).
Proof. exact (@lem3207365 (@IN _83983 _32951 s)). Qed.
Lemma lem3207367 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3207368 {_83983 : Type'} (_32951 : _83983) (s : _83983 -> Prop) : (term195 _83983 _32951 s) = (term196 _83983 _32951 s).
Proof. exact (MK_COMB (@lem3207367) (@lem3207366 _83983 _32951 s)). Qed.
Lemma lem3207369 {_83983 : Type'} (P : _83983 -> Prop) (_32951 : _83983) : (P _32951) = (P _32951).
Proof. exact (eq_refl (P _32951)). Qed.
Lemma lem3207370 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (_32951 : _83983) : (term193 _83983 s P _32951) = (term38 _83983 s P _32951).
Proof. exact (MK_COMB (@lem3207368 _83983 _32951 s) (@lem3207369 _83983 P _32951)). Qed.
Lemma lem3207371 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (_32951 : _83983) : (term190 _83983 P _32951 s) = (term38 _83983 s P _32951).
Proof. exact (TRANS (@lem3207363 _83983 s P _32951) (@lem3207370 _83983 s P _32951)). Qed.
Lemma lem3207374 {_83983 : Type'} (_32951 : _83983) (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term38 _83983 s P _32951.
Proof. exact (EQ_MP (@lem3207371 _83983 s P _32951) (@lem3207360 _83983 _32951 x a s P h1)). Qed.
Lemma lem3207375 {_83983 : Type'} (_32951 : _83983) (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term38 _83983 s P _32951.
Proof. exact (@lem3207374 _83983 _32951 x a s P h1). Qed.
Lemma lem3207376 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term38 _83983 s P x.
Proof. exact (@lem3207375 _83983 x x a s P h1). Qed.
Lemma lem3207379 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : P x.
Proof. exact (@lem3207376 _83983 x a s P h1 (@lem3207331 _83983 x s h2)). Qed.
Lemma lem3207380 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : term186 _83983 P x.
Proof. exact (fun h0 : term96 _83983 P x => @lem3207379 _83983 a P x s h1 h2). Qed.
Lemma lem3207382 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207383 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) : (term186 _83983 P x) = (P x).
Proof. exact (@lem3207382 (P x)). Qed.
Lemma lem3207384 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : P x.
Proof. exact (EQ_MP (@lem3207383 _83983 P x) (@lem3207380 _83983 a P x s h1 h2)). Qed.
Lemma lem3207387 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3207389 {_83983 : Type'} (P : _83983 -> Prop) (x : _83983) : (term96 _83983 P x) = (term187 _83983 P x).
Proof. exact (@lem3207387 (P x)). Qed.
Lemma lem3207392 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : term187 _83983 P x.
Proof. exact (EQ_MP (@lem3207389 _83983 P x) (@lem3207016 _83983 x a s P h1)). Qed.
Lemma lem3207395 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : False.
Proof. exact (@lem3207392 _83983 x a s P h1 (@lem3207384 _83983 a P x s h1 h2)). Qed.
Lemma lem3207396 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : term188.
Proof. exact (fun h0 : ~ False => @lem3207395 _83983 a P x s h1 h2). Qed.
Lemma lem3207398 (p : Prop) : (term175 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3207399 : term188 = False.
Proof. exact (@lem3207398 False). Qed.
Lemma lem3207400 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : False.
Proof. exact (EQ_MP (@lem3207399) (@lem3207396 _83983 a P x s h1 h2)). Qed.
Lemma lem3207401 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3207323) (@lem3207320 _83983 s P x a h1 h2)). Qed.
Lemma lem3207402 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : (@IN _83983 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _83983 x s => @lem3207400 _83983 a P x s h1 h2) (fun h3 : False => @lem3207018 _83983 x s h2)). Qed.
Lemma lem3207403 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : False.
Proof. exact (EQ_MP (@lem3207402 _83983 a P x s h1 h2) (@lem3207018 _83983 x s h2)). Qed.
Lemma lem3207404 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3207401 _83983 s P x a h1 h2) (fun h3 : False => @lem3207006 _83983 x a h2)). Qed.
Lemma lem3207405 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3207404 _83983 s P x a h1 h2) (@lem3207006 _83983 x a h2)). Qed.
Lemma lem3207406 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term96 _83983 P a) (h2 : term118 _83983 a s P x) : (term96 _83983 P a) = False.
Proof. exact (prop_ext (fun h3 : term96 _83983 P a => @lem3207190 _83983 a s P x h1 h2) (fun h3 : False => @lem3206966 _83983 P a h1)). Qed.
Lemma lem3207407 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term96 _83983 P a) (h2 : term118 _83983 a s P x) : False.
Proof. exact (EQ_MP (@lem3207406 _83983 a s P x h1 h2) (@lem3206966 _83983 P a h1)). Qed.
Lemma lem3207408 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : (@IN _83983 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _83983 x s => @lem3207403 _83983 a P x s h1 h2) (fun h3 : False => @lem3206948 _83983 x s h2)). Qed.
Lemma lem3207409 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : False.
Proof. exact (EQ_MP (@lem3207408 _83983 a P x s h1 h2) (@lem3206948 _83983 x s h2)). Qed.
Lemma lem3207410 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3207405 _83983 s P x a h1 h2) (fun h3 : False => @lem3206923 _83983 x a h2)). Qed.
Lemma lem3207411 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3207410 _83983 s P x a h1 h2) (@lem3206923 _83983 x a h2)). Qed.
Lemma lem3207412 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term96 _83983 P a) (h2 : term118 _83983 a s P x) : (term96 _83983 P a) = False.
Proof. exact (prop_ext (fun h3 : term96 _83983 P a => @lem3207407 _83983 a s P x h1 h2) (fun h3 : False => @lem3206867 _83983 P a h1)). Qed.
Lemma lem3207413 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term96 _83983 P a) (h2 : term118 _83983 a s P x) : False.
Proof. exact (EQ_MP (@lem3207412 _83983 a s P x h1 h2) (@lem3206867 _83983 P a h1)). Qed.
Lemma lem3207414 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : (@IN _83983 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _83983 x s => @lem3207409 _83983 a P x s h1 h2) (fun h3 : False => @lem3206948 _83983 x s h2)). Qed.
Lemma lem3207415 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (x : _83983) (s : _83983 -> Prop) (h1 : term136 _83983 x a s P) (h2 : @IN _83983 x s) : False.
Proof. exact (EQ_MP (@lem3207414 _83983 a P x s h1 h2) (@lem3206948 _83983 x s h2)). Qed.
Lemma lem3207416 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3207411 _83983 s P x a h1 h2) (fun h3 : False => @lem3206923 _83983 x a h2)). Qed.
Lemma lem3207417 {_83983 : Type'} (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (a : _83983) (h1 : term136 _83983 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3207416 _83983 s P x a h1 h2) (@lem3206923 _83983 x a h2)). Qed.
Lemma lem3207418 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term96 _83983 P a) (h2 : term118 _83983 a s P x) : (term96 _83983 P a) = False.
Proof. exact (prop_ext (fun h3 : term96 _83983 P a => @lem3207413 _83983 a s P x h1 h2) (fun h3 : False => @lem3206867 _83983 P a h1)). Qed.
Lemma lem3207419 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term96 _83983 P a) (h2 : term118 _83983 a s P x) : False.
Proof. exact (EQ_MP (@lem3207418 _83983 a s P x h1 h2) (@lem3206867 _83983 P a h1)). Qed.
Lemma lem3207420 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term136 _83983 x a s P) : False.
Proof. exact (or_elim (@lem3206838 _83983 x a s P h1) (fun h0 : x = a => @lem3207417 _83983 s P x a h1 h0) (fun h0 : @IN _83983 x s => @lem3207415 _83983 a P x s h1 h0)). Qed.
Lemma lem3207421 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (x : _83983) (h1 : term118 _83983 a s P x) : False.
Proof. exact (or_elim (@lem3206827 _83983 a s P x h1) (fun h0 : term96 _83983 P a => @lem3207419 _83983 a s P x h0 h1) (fun h0 : term64 _83983 s P x => @lem3207301 _83983 a s P x h1 h0)). Qed.
Lemma lem3207422 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term157 _83983 x a s P) : False.
Proof. exact (or_elim (@lem3206824 _83983 x a s P h1) (fun h0 : term118 _83983 a s P x => @lem3207421 _83983 a s P x h0) (fun h0 : term136 _83983 x a s P => @lem3207420 _83983 x a s P h0)). Qed.
Lemma lem3207423 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term157 _83983 x a s P) : (term157 _83983 x a s P) = False.
Proof. exact (prop_ext (fun h2 : term157 _83983 x a s P => @lem3207422 _83983 x a s P h1) (fun h2 : False => @lem3206824 _83983 x a s P h1)). Qed.
Lemma lem3207424 {_83983 : Type'} (x : _83983) (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term157 _83983 x a s P) : False.
Proof. exact (EQ_MP (@lem3207423 _83983 x a s P h1) (@lem3206824 _83983 x a s P h1)). Qed.
Lemma lem3207425 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term43 _83983 a s P) : False.
Proof. exact (ex_elim (@lem3206723 _83983 a s P h1) (fun x : _83983 => fun h0 : term159 _83983 a s P x => @lem3207424 _83983 x a s P h0)). Qed.
Lemma lem3207426 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term43 _83983 a s P) : (term43 _83983 a s P) = False.
Proof. exact (prop_ext (fun h2 : term43 _83983 a s P => @lem3207425 _83983 a s P h1) (fun h2 : False => @lem3206376 _83983 a s P h1)). Qed.
Lemma lem3207427 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) (h1 : term43 _83983 a s P) : False.
Proof. exact (EQ_MP (@lem3207426 _83983 a s P h1) (@lem3206376 _83983 a s P h1)). Qed.
Lemma lem3207428 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : term42 _83983 a s P.
Proof. exact (fun h0 : term43 _83983 a s P => @lem3207427 _83983 a s P h0). Qed.
Lemma lem3207429 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term14 _83983 a s P) = (term17 _83983 a s P).
Proof. exact (EQ_MP (@lem3206375 _83983 a s P) (@lem3207428 _83983 a s P)). Qed.
Lemma lem3207434 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term21 _83983 a P.
Proof. exact (fun s : _83983 -> Prop => @lem3207429 _83983 a s P). Qed.
Lemma lem3207439 {_83983 : Type'} (P : _83983 -> Prop) : term25 _83983 P.
Proof. exact (fun a : _83983 => @lem3207434 _83983 a P). Qed.
Lemma lem3207444 {_83983 : Type'} : term29 _83983.
Proof. exact (fun P : _83983 -> Prop => @lem3207439 _83983 P). Qed.
Lemma lem3207445 {_83983 : Type'} : term31 _83983.
Proof. exact (EQ_MP (@lem3206371 _83983) (@lem3207444 _83983)). Qed.
Lemma lem3207447 {_83983 : Type'} : term31 _83983.
Proof. exact (@lem3206254 _83983 (@lem3207445 _83983)). Qed.
Lemma lem3207448 {_83983 : Type'} (h1 : term32 _83983) : False.
Proof. exact (@lem3207447 _83983 (@lem3206238 _83983 h1)). Qed.
Lemma lem3207449 {_83983 : Type'} (h1 : term32 _83983) : (term32 _83983) = False.
Proof. exact (prop_ext (fun h2 : term32 _83983 => @lem3207448 _83983 h1) (fun h2 : False => @lem3206238 _83983 h1)). Qed.
Lemma lem3207450 {_83983 : Type'} (h1 : term32 _83983) : False.
Proof. exact (EQ_MP (@lem3207449 _83983 h1) (@lem3206238 _83983 h1)). Qed.
Lemma lem3207451 {_83983 : Type'} : term31 _83983.
Proof. exact (fun h0 : term32 _83983 => @lem3207450 _83983 h0). Qed.
Lemma lem3207452 {_83983 : Type'} : term29 _83983.
Proof. exact (EQ_MP (@lem3206237 _83983) (@lem3207451 _83983)). Qed.
Lemma lem3207453 {_83983 : Type'} : term28 _83983.
Proof. exact (EQ_MP (@lem3206233 _83983) (@lem3207452 _83983)). Qed.
