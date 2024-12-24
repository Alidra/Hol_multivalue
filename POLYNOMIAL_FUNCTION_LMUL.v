Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_LMUL_term_abbrevs.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import SUM_LMUL_spec.
Require Import polynomial_function_spec.
Require Import thm0_spec.
Require Import thm1338912_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem7567174 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem7567175 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem7567174 x y z h1)). Qed.
Lemma lem7567176 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem7567177 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem7567176 x y z h1)). Qed.
Lemma lem7567178 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem7567175 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem7567177 x y z h1)). Qed.
Lemma lem7567179 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem7567178 x y z)). Qed.
Lemma lem7567180 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7567181 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem7567180) (@lem7567179 x y)). Qed.
Lemma lem7567182 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem7567181 x y)). Qed.
Lemma lem7567183 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7567184 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem7567183) (@lem7567182 x)). Qed.
Lemma lem7567185 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem7567184 x)). Qed.
Lemma lem7567186 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7567187 : term12 = term13.
Proof. exact (MK_COMB (@lem7567186) (@lem7567185)). Qed.
Lemma lem7567188 : term13.
Proof. exact (EQ_MP (@lem7567187) (@lem1338912)). Qed.
Lemma lem7567189 {A : Type'} (P : A -> Prop) : term14 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem7567190 {A : Type'} (P : A -> Prop) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem7567191 {A : Type'} (P : A -> Prop) : term15 A P.
Proof. exact (EQ_MP (@lem7567190 A P) (@lem7567189 A P)). Qed.
Lemma lem7567192 {A : Type'} (P : A -> Prop) (Q : Prop) : term16 A P Q.
Proof. exact (@lem7567191 A P Q). Qed.
Lemma lem7567193 {A : Type'} (P : A -> Prop) (Q : Prop) : (term16 A P Q) = ((term17 A P Q) = (term18 A P Q)).
Proof. exact (eq_refl (term16 A P Q)). Qed.
Lemma lem7567195 (p : real -> real) : term19 p.
Proof. exact (@lem7553488 p). Qed.
Lemma lem7567196 (p : real -> real) : (term19 p) = ((polynomial_function p) = (term20 p)).
Proof. exact (eq_refl (term19 p)). Qed.
Lemma lem7567201 (p : real -> real) : (polynomial_function p) = (term20 p).
Proof. exact (EQ_MP (@lem7567196 p) (@lem7567195 p)). Qed.
Lemma lem7567216 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7567217 (p : real -> real) : (term21 p) = (term22 p).
Proof. exact (MK_COMB (@lem7567216) (@lem7567201 p)). Qed.
Lemma lem7567219 (p : real -> real) : (polynomial_function p) = (term20 p).
Proof. exact (EQ_MP (@lem7567196 p) (@lem7567195 p)). Qed.
Lemma lem7567220 (c : real) (p : real -> real) : (term23 c p) = (term24 c p).
Proof. exact (@lem7567219 (term25 c p)). Qed.
Lemma lem7567236 {A B : Type'} (f : A -> B) (y : A) : (term26 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7567237 (f : real -> real) (y : real) : (term27 f y) = (f y).
Proof. exact (@lem7567236 real real f y). Qed.
Lemma lem7567238 (c : real) (p : real -> real) (x : real) : (term28 c p x) = (term29 c p x).
Proof. exact (@lem7567237 (term25 c p) x). Qed.
Lemma lem7567239 (c : real) (p : real -> real) (x : real) : (term29 c p x) = (term30 c p x).
Proof. exact (eq_refl (term29 c p x)). Qed.
Lemma lem7567240 (c : real) (p : real -> real) : (term31 c p) = (term25 c p).
Proof. exact (fun_ext (fun x : real => @lem7567239 c p x)). Qed.
Lemma lem7567241 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7567242 (c : real) (p : real -> real) (x : real) : (term28 c p x) = (term29 c p x).
Proof. exact (MK_COMB (@lem7567240 c p) (@lem7567241 x)). Qed.
Lemma lem7567243 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7567244 (c : real) (p : real -> real) (x : real) : (term32 c p x) = (term33 c p x).
Proof. exact (MK_COMB (@lem7567243) (@lem7567242 c p x)). Qed.
Lemma lem7567245 (c : real) (p : real -> real) (x : real) : (term29 c p x) = (term30 c p x).
Proof. exact (eq_refl (term29 c p x)). Qed.
Lemma lem7567246 (c : real) (p : real -> real) (x : real) : ((term28 c p x) = (term29 c p x)) = ((term29 c p x) = (term30 c p x)).
Proof. exact (MK_COMB (@lem7567244 c p x) (@lem7567245 c p x)). Qed.
Lemma lem7567247 (c : real) (p : real -> real) (x : real) : (term29 c p x) = (term30 c p x).
Proof. exact (EQ_MP (@lem7567246 c p x) (@lem7567238 c p x)). Qed.
Lemma lem7567248 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7567249 (c : real) (p : real -> real) (x : real) : (term33 c p x) = (term34 c p x).
Proof. exact (MK_COMB (@lem7567248) (@lem7567247 c p x)). Qed.
Lemma lem7567250 (m : nat) (c : nat -> real) (x : real) : (term35 m c x) = (term35 m c x).
Proof. exact (eq_refl (term35 m c x)). Qed.
Lemma lem7567251 (c : real) (p : real -> real) (m : nat) (c' : nat -> real) (x : real) : ((term29 c p x) = (term35 m c' x)) = ((term30 c p x) = (term35 m c' x)).
Proof. exact (MK_COMB (@lem7567249 c p x) (@lem7567250 m c' x)). Qed.
Lemma lem7567254 (c : real) (p : real -> real) (m : nat) (c' : nat -> real) : (term36 c p m c') = (term37 c p m c').
Proof. exact (fun_ext (fun x : real => @lem7567251 c p m c' x)). Qed.
Lemma lem7567255 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7567256 (c : real) (p : real -> real) (m : nat) (c' : nat -> real) : (term38 c p m c') = (term39 c p m c').
Proof. exact (MK_COMB (@lem7567255) (@lem7567254 c p m c')). Qed.
Lemma lem7567261 (c : real) (p : real -> real) (m : nat) : (term40 c p m) = (term41 c p m).
Proof. exact (fun_ext (fun c' : nat -> real => @lem7567256 c p m c')). Qed.
Lemma lem7567262 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7567263 (c : real) (p : real -> real) (m : nat) : (term42 c p m) = (term43 c p m).
Proof. exact (MK_COMB (@lem7567262) (@lem7567261 c p m)). Qed.
Lemma lem7567268 (c : real) (p : real -> real) : (term44 c p) = (term45 c p).
Proof. exact (fun_ext (fun m : nat => @lem7567263 c p m)). Qed.
Lemma lem7567269 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7567270 (c : real) (p : real -> real) : (term24 c p) = (term46 c p).
Proof. exact (MK_COMB (@lem7567269) (@lem7567268 c p)). Qed.
Lemma lem7567275 (c : real) (p : real -> real) : (term23 c p) = (term46 c p).
Proof. exact (TRANS (@lem7567220 c p) (@lem7567270 c p)). Qed.
Lemma lem7567276 (c : real) (p : real -> real) : (term47 c p) = (term48 c p).
Proof. exact (MK_COMB (@lem7567217 p) (@lem7567275 c p)). Qed.
Lemma lem7567278 {A : Type'} (P : A -> Prop) (Q : Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7567193 A P Q) (@lem7567192 A P Q)). Qed.
Lemma lem7567279 (P : nat -> Prop) (Q : Prop) : (term49 P Q) = (term50 P Q).
Proof. exact (@lem7567278 nat P Q). Qed.
Lemma lem7567280 (c : real) (p : real -> real) : (term51 c p) = (term52 c p).
Proof. exact (@lem7567279 (term53 p) (term46 c p)). Qed.
Lemma lem7567281 (p : real -> real) (m : nat) : (term54 p m) = (term55 p m).
Proof. exact (eq_refl (term54 p m)). Qed.
Lemma lem7567282 (p : real -> real) : (term56 p) = (term53 p).
Proof. exact (fun_ext (fun m : nat => @lem7567281 p m)). Qed.
Lemma lem7567283 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7567284 (p : real -> real) : (term57 p) = (term20 p).
Proof. exact (MK_COMB (@lem7567283) (@lem7567282 p)). Qed.
Lemma lem7567285 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7567286 (p : real -> real) : (term58 p) = (term22 p).
Proof. exact (MK_COMB (@lem7567285) (@lem7567284 p)). Qed.
Lemma lem7567287 (c : real) (p : real -> real) : (term46 c p) = (term46 c p).
Proof. exact (eq_refl (term46 c p)). Qed.
Lemma lem7567288 (c : real) (p : real -> real) : (term51 c p) = (term48 c p).
Proof. exact (MK_COMB (@lem7567286 p) (@lem7567287 c p)). Qed.
Lemma lem7567289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7567290 (c : real) (p : real -> real) : (term59 c p) = (term60 c p).
Proof. exact (MK_COMB (@lem7567289) (@lem7567288 c p)). Qed.
Lemma lem7567291 (p : real -> real) (m : nat) : (term54 p m) = (term55 p m).
Proof. exact (eq_refl (term54 p m)). Qed.
Lemma lem7567292 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7567293 (p : real -> real) (m : nat) : (term61 p m) = (term62 p m).
Proof. exact (MK_COMB (@lem7567292) (@lem7567291 p m)). Qed.
Lemma lem7567294 (c : real) (p : real -> real) : (term46 c p) = (term46 c p).
Proof. exact (eq_refl (term46 c p)). Qed.
Lemma lem7567295 (m : nat) (c : real) (p : real -> real) : (term63 m c p) = (term64 m c p).
Proof. exact (MK_COMB (@lem7567293 p m) (@lem7567294 c p)). Qed.
Lemma lem7567296 (c : real) (p : real -> real) : (term65 c p) = (term66 c p).
Proof. exact (fun_ext (fun m : nat => @lem7567295 m c p)). Qed.
Lemma lem7567297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7567298 (c : real) (p : real -> real) : (term52 c p) = (term67 c p).
Proof. exact (MK_COMB (@lem7567297) (@lem7567296 c p)). Qed.
Lemma lem7567299 (c : real) (p : real -> real) : ((term51 c p) = (term52 c p)) = ((term48 c p) = (term67 c p)).
Proof. exact (MK_COMB (@lem7567290 c p) (@lem7567298 c p)). Qed.
Lemma lem7567300 (c : real) (p : real -> real) : (term48 c p) = (term67 c p).
Proof. exact (EQ_MP (@lem7567299 c p) (@lem7567280 c p)). Qed.
Lemma lem7567306 {A : Type'} (P : A -> Prop) (Q : Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7567193 A P Q) (@lem7567192 A P Q)). Qed.
Lemma lem7567307 (P : type1010) (Q : Prop) : (term68 P Q) = (term69 P Q).
Proof. exact (@lem7567306 (nat -> real) P Q). Qed.
Lemma lem7567308 (m : nat) (c : real) (p : real -> real) : (term70 m c p) = (term71 m c p).
Proof. exact (@lem7567307 (term72 p m) (term46 c p)). Qed.
Lemma lem7567309 (p : real -> real) (m : nat) (c : nat -> real) : (term73 p m c) = (term74 p m c).
Proof. exact (eq_refl (term73 p m c)). Qed.
Lemma lem7567310 (p : real -> real) (m : nat) : (term75 p m) = (term72 p m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7567309 p m c)). Qed.
Lemma lem7567311 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7567312 (p : real -> real) (m : nat) : (term76 p m) = (term55 p m).
Proof. exact (MK_COMB (@lem7567311) (@lem7567310 p m)). Qed.
Lemma lem7567313 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7567314 (p : real -> real) (m : nat) : (term77 p m) = (term62 p m).
Proof. exact (MK_COMB (@lem7567313) (@lem7567312 p m)). Qed.
Lemma lem7567315 (c : real) (p : real -> real) : (term46 c p) = (term46 c p).
Proof. exact (eq_refl (term46 c p)). Qed.
Lemma lem7567316 (m : nat) (c : real) (p : real -> real) : (term70 m c p) = (term64 m c p).
Proof. exact (MK_COMB (@lem7567314 p m) (@lem7567315 c p)). Qed.
Lemma lem7567317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7567318 (m : nat) (c : real) (p : real -> real) : (term78 m c p) = (term79 m c p).
Proof. exact (MK_COMB (@lem7567317) (@lem7567316 m c p)). Qed.
Lemma lem7567319 (p : real -> real) (m : nat) (c : nat -> real) : (term73 p m c) = (term74 p m c).
Proof. exact (eq_refl (term73 p m c)). Qed.
Lemma lem7567320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7567321 (p : real -> real) (m : nat) (c : nat -> real) : (term80 p m c) = (term81 p m c).
Proof. exact (MK_COMB (@lem7567320) (@lem7567319 p m c)). Qed.
Lemma lem7567322 (c : real) (p : real -> real) : (term46 c p) = (term46 c p).
Proof. exact (eq_refl (term46 c p)). Qed.
Lemma lem7567323 (m : nat) (c : nat -> real) (c' : real) (p : real -> real) : (term82 m c c' p) = (term83 m c c' p).
Proof. exact (MK_COMB (@lem7567321 p m c) (@lem7567322 c' p)). Qed.
Lemma lem7567324 (m : nat) (c : real) (p : real -> real) : (term84 m c p) = (term85 m c p).
Proof. exact (fun_ext (fun c' : nat -> real => @lem7567323 m c' c p)). Qed.
Lemma lem7567325 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7567326 (m : nat) (c : real) (p : real -> real) : (term71 m c p) = (term86 m c p).
Proof. exact (MK_COMB (@lem7567325) (@lem7567324 m c p)). Qed.
Lemma lem7567327 (m : nat) (c : real) (p : real -> real) : ((term70 m c p) = (term71 m c p)) = ((term64 m c p) = (term86 m c p)).
Proof. exact (MK_COMB (@lem7567318 m c p) (@lem7567326 m c p)). Qed.
Lemma lem7567328 (m : nat) (c : real) (p : real -> real) : (term64 m c p) = (term86 m c p).
Proof. exact (EQ_MP (@lem7567327 m c p) (@lem7567308 m c p)). Qed.
Lemma lem7567355 (c : real) (p : real -> real) : (term66 c p) = (term87 c p).
Proof. exact (fun_ext (fun m : nat => @lem7567328 m c p)). Qed.
Lemma lem7567356 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7567357 (c : real) (p : real -> real) : (term67 c p) = (term88 c p).
Proof. exact (MK_COMB (@lem7567356) (@lem7567355 c p)). Qed.
Lemma lem7567362 (c : real) (p : real -> real) : (term48 c p) = (term88 c p).
Proof. exact (TRANS (@lem7567300 c p) (@lem7567357 c p)). Qed.
Lemma lem7567363 (c : real) (p : real -> real) : (term47 c p) = (term88 c p).
Proof. exact (TRANS (@lem7567276 c p) (@lem7567362 c p)). Qed.
Lemma lem7567364 (c : real) (p : real -> real) : (term88 c p) = (term47 c p).
Proof. exact (SYM (@lem7567363 c p)). Qed.
Lemma lem7567365 (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : term74 p n a.
Proof. exact (h1). Qed.
Lemma lem7567366 (x : real) : term89 x.
Proof. exact (@lem7567188 x). Qed.
Lemma lem7567367 (x : real) : (term89 x) = (term9 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem7567368 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem7567367 x) (@lem7567366 x)). Qed.
Lemma lem7567369 (x : real) (y : real) : term90 x y.
Proof. exact (@lem7567368 x y). Qed.
Lemma lem7567370 (x : real) (y : real) : (term90 x y) = (term5 x y).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem7567371 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem7567370 x y) (@lem7567369 x y)). Qed.
Lemma lem7567372 (x : real) (y : real) (z : real) : term91 x y z.
Proof. exact (@lem7567371 x y z). Qed.
Lemma lem7567373 (x : real) (y : real) (z : real) : (term91 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term91 x y z)). Qed.
Lemma lem7567375 {A : Type'} (f : A -> real) : term92 A f.
Proof. exact (@lem7070264 A f). Qed.
Lemma lem7567376 {A : Type'} (f : A -> real) : (term92 A f) = (term93 A f).
Proof. exact (eq_refl (term92 A f)). Qed.
Lemma lem7567377 {A : Type'} (f : A -> real) : term93 A f.
Proof. exact (EQ_MP (@lem7567376 A f) (@lem7567375 A f)). Qed.
Lemma lem7567378 {A : Type'} (f : A -> real) (c : real) : term94 A f c.
Proof. exact (@lem7567377 A f c). Qed.
Lemma lem7567379 {A : Type'} (c : real) (f : A -> real) : (term94 A f c) = (term95 A c f).
Proof. exact (eq_refl (term94 A f c)). Qed.
Lemma lem7567380 {A : Type'} (c : real) (f : A -> real) : term95 A c f.
Proof. exact (EQ_MP (@lem7567379 A c f) (@lem7567378 A f c)). Qed.
Lemma lem7567381 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) : term96 A c f s.
Proof. exact (@lem7567380 A c f s). Qed.
Lemma lem7567382 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term96 A c f s) = ((term97 A s c f) = (term98 A c s f)).
Proof. exact (eq_refl (term96 A c f s)). Qed.
Lemma lem7567384 (x : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : term99 p n a x.
Proof. exact (@lem7567365 p n a h1 x). Qed.
Lemma lem7567385 (p : real -> real) (n : nat) (a : nat -> real) (x : real) : (term99 p n a x) = ((p x) = (term35 n a x)).
Proof. exact (eq_refl (term99 p n a x)). Qed.
Lemma lem7567394 (x : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : (p x) = (term35 n a x).
Proof. exact (EQ_MP (@lem7567385 p n a x) (@lem7567384 x p n a h1)). Qed.
Lemma lem7567410 (c : real) : (real_mul c) = (real_mul c).
Proof. exact (eq_refl (real_mul c)). Qed.
Lemma lem7567411 (c : real) (x : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : (term30 c p x) = (term100 c n a x).
Proof. exact (MK_COMB (@lem7567410 c) (@lem7567394 x p n a h1)). Qed.
Lemma lem7567412 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7567413 (c : real) (x : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : (term34 c p x) = (term101 c n a x).
Proof. exact (MK_COMB (@lem7567412) (@lem7567411 c x p n a h1)). Qed.
Lemma lem7567430 {A B : Type'} (f : A -> B) (y : A) : (term26 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7567431 (f : nat -> real) (y : nat) : (term102 f y) = (f y).
Proof. exact (@lem7567430 nat real f y). Qed.
Lemma lem7567432 (c : real) (a : nat -> real) (i : nat) : (term103 c a i) = (term104 c a i).
Proof. exact (@lem7567431 (term105 c a) i). Qed.
Lemma lem7567433 (c : real) (a : nat -> real) (i : nat) : (term104 c a i) = (term106 c a i).
Proof. exact (eq_refl (term104 c a i)). Qed.
Lemma lem7567434 (c : real) (a : nat -> real) : (term107 c a) = (term105 c a).
Proof. exact (fun_ext (fun i : nat => @lem7567433 c a i)). Qed.
Lemma lem7567435 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7567436 (c : real) (a : nat -> real) (i : nat) : (term103 c a i) = (term104 c a i).
Proof. exact (MK_COMB (@lem7567434 c a) (@lem7567435 i)). Qed.
Lemma lem7567437 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7567438 (c : real) (a : nat -> real) (i : nat) : (term108 c a i) = (term109 c a i).
Proof. exact (MK_COMB (@lem7567437) (@lem7567436 c a i)). Qed.
Lemma lem7567439 (c : real) (a : nat -> real) (i : nat) : (term104 c a i) = (term106 c a i).
Proof. exact (eq_refl (term104 c a i)). Qed.
Lemma lem7567440 (c : real) (a : nat -> real) (i : nat) : ((term103 c a i) = (term104 c a i)) = ((term104 c a i) = (term106 c a i)).
Proof. exact (MK_COMB (@lem7567438 c a i) (@lem7567439 c a i)). Qed.
Lemma lem7567441 (c : real) (a : nat -> real) (i : nat) : (term104 c a i) = (term106 c a i).
Proof. exact (EQ_MP (@lem7567440 c a i) (@lem7567432 c a i)). Qed.
Lemma lem7567442 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7567443 (c : real) (a : nat -> real) (i : nat) : (term110 c a i) = (term111 c a i).
Proof. exact (MK_COMB (@lem7567442) (@lem7567441 c a i)). Qed.
Lemma lem7567444 (x : real) (i : nat) : (real_pow x i) = (real_pow x i).
Proof. exact (eq_refl (real_pow x i)). Qed.
Lemma lem7567445 (c : real) (a : nat -> real) (x : real) (i : nat) : (term112 c a x i) = (term113 c a x i).
Proof. exact (MK_COMB (@lem7567443 c a i) (@lem7567444 x i)). Qed.
Lemma lem7567447 (x : real) (y : real) (z : real) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem7567373 x y z) (@lem7567372 x y z)). Qed.
Lemma lem7567448 (c : real) (a : nat -> real) (x : real) (i : nat) : (term113 c a x i) = (term114 c a x i).
Proof. exact (@lem7567447 c (a i) (real_pow x i)). Qed.
Lemma lem7567449 (c : real) (a : nat -> real) (x : real) (i : nat) : (term112 c a x i) = (term114 c a x i).
Proof. exact (TRANS (@lem7567445 c a x i) (@lem7567448 c a x i)). Qed.
Lemma lem7567450 (c : real) (a : nat -> real) (x : real) : (term115 c a x) = (term116 c a x).
Proof. exact (fun_ext (fun i : nat => @lem7567449 c a x i)). Qed.
Lemma lem7567451 (n : nat) : (term117 n) = (term117 n).
Proof. exact (eq_refl (term117 n)). Qed.
Lemma lem7567452 (n : nat) (c : real) (a : nat -> real) (x : real) : (term118 n c a x) = (term119 n c a x).
Proof. exact (MK_COMB (@lem7567451 n) (@lem7567450 c a x)). Qed.
Lemma lem7567454 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term97 A s c f) = (term98 A c s f).
Proof. exact (EQ_MP (@lem7567382 A c s f) (@lem7567381 A c f s)). Qed.
Lemma lem7567455 (c : real) (s : nat -> Prop) (f : nat -> real) : (term120 s c f) = (term121 c s f).
Proof. exact (@lem7567454 nat c s f). Qed.
Lemma lem7567456 (c : real) (n : nat) (a : nat -> real) (x : real) : (term122 n c a x) = (term100 c n a x).
Proof. exact (@lem7567455 c (term123 n) (term124 a x)). Qed.
Lemma lem7567457 (a : nat -> real) (x : real) (i : nat) : (term125 a x i) = (term126 a x i).
Proof. exact (eq_refl (term125 a x i)). Qed.
Lemma lem7567458 (c : real) : (real_mul c) = (real_mul c).
Proof. exact (eq_refl (real_mul c)). Qed.
Lemma lem7567459 (c : real) (a : nat -> real) (x : real) (i : nat) : (term127 c a x i) = (term114 c a x i).
Proof. exact (MK_COMB (@lem7567458 c) (@lem7567457 a x i)). Qed.
Lemma lem7567460 (c : real) (a : nat -> real) (x : real) : (term128 c a x) = (term116 c a x).
Proof. exact (fun_ext (fun i : nat => @lem7567459 c a x i)). Qed.
Lemma lem7567461 (n : nat) : (term117 n) = (term117 n).
Proof. exact (eq_refl (term117 n)). Qed.
Lemma lem7567462 (n : nat) (c : real) (a : nat -> real) (x : real) : (term122 n c a x) = (term119 n c a x).
Proof. exact (MK_COMB (@lem7567461 n) (@lem7567460 c a x)). Qed.
Lemma lem7567463 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7567464 (n : nat) (c : real) (a : nat -> real) (x : real) : (term129 n c a x) = (term130 n c a x).
Proof. exact (MK_COMB (@lem7567463) (@lem7567462 n c a x)). Qed.
Lemma lem7567465 (c : real) (n : nat) (a : nat -> real) (x : real) : (term100 c n a x) = (term100 c n a x).
Proof. exact (eq_refl (term100 c n a x)). Qed.
Lemma lem7567466 (c : real) (n : nat) (a : nat -> real) (x : real) : ((term122 n c a x) = (term100 c n a x)) = ((term119 n c a x) = (term100 c n a x)).
Proof. exact (MK_COMB (@lem7567464 n c a x) (@lem7567465 c n a x)). Qed.
Lemma lem7567467 (c : real) (n : nat) (a : nat -> real) (x : real) : (term119 n c a x) = (term100 c n a x).
Proof. exact (EQ_MP (@lem7567466 c n a x) (@lem7567456 c n a x)). Qed.
Lemma lem7567483 (c : real) (n : nat) (a : nat -> real) (x : real) : (term118 n c a x) = (term100 c n a x).
Proof. exact (TRANS (@lem7567452 n c a x) (@lem7567467 c n a x)). Qed.
Lemma lem7567484 (c : real) (x : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : ((term30 c p x) = (term118 n c a x)) = ((term100 c n a x) = (term100 c n a x)).
Proof. exact (MK_COMB (@lem7567413 c x p n a h1) (@lem7567483 c n a x)). Qed.
Lemma lem7567486 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7567487 (x : real) : (x = x) = True.
Proof. exact (@lem7567486 real x). Qed.
Lemma lem7567488 (c : real) (n : nat) (a : nat -> real) (x : real) : ((term100 c n a x) = (term100 c n a x)) = True.
Proof. exact (@lem7567487 (term100 c n a x)). Qed.
Lemma lem7567489 (c : real) (x : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : ((term30 c p x) = (term118 n c a x)) = True.
Proof. exact (TRANS (@lem7567484 c x p n a h1) (@lem7567488 c n a x)). Qed.
Lemma lem7567490 (c : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : (term131 p n c a) = term132.
Proof. exact (fun_ext (fun x : real => @lem7567489 c x p n a h1)). Qed.
Lemma lem7567491 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7567492 (c : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : (term133 p n c a) = term134.
Proof. exact (MK_COMB (@lem7567491) (@lem7567490 c p n a h1)). Qed.
Lemma lem7567494 {A : Type'} (t : Prop) : (term135 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7567495 (t : Prop) : (term136 t) = t.
Proof. exact (@lem7567494 real t). Qed.
Lemma lem7567496 : term134 = True.
Proof. exact (@lem7567495 True). Qed.
Lemma lem7567497 (c : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : (term133 p n c a) = True.
Proof. exact (TRANS (@lem7567492 c p n a h1) (@lem7567496)). Qed.
Lemma lem7567498 (c : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : True = (term133 p n c a).
Proof. exact (SYM (@lem7567497 c p n a h1)). Qed.
Lemma lem7567499 (c : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : term133 p n c a.
Proof. exact (EQ_MP (@lem7567498 c p n a h1) (@lem0)). Qed.
Lemma lem7567500 (c : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : term43 c p n.
Proof. exact (ex_intro (term41 c p n) (term105 c a) (@lem7567499 c p n a h1)). Qed.
Lemma lem7567501 (c : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : term46 c p.
Proof. exact (ex_intro (term45 c p) n (@lem7567500 c p n a h1)). Qed.
Lemma lem7567502 (c : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : (term74 p n a) = (term46 c p).
Proof. exact (prop_ext (fun h2 : term74 p n a => @lem7567501 c p n a h1) (fun h2 : term46 c p => @lem7567365 p n a h1)). Qed.
Lemma lem7567503 (c : real) (p : real -> real) (n : nat) (a : nat -> real) (h1 : term74 p n a) : term46 c p.
Proof. exact (EQ_MP (@lem7567502 c p n a h1) (@lem7567365 p n a h1)). Qed.
Lemma lem7567504 (n : nat) (a : nat -> real) (c : real) (p : real -> real) : term83 n a c p.
Proof. exact (fun h0 : term74 p n a => @lem7567503 c p n a h0). Qed.
Lemma lem7567509 (n : nat) (c : real) (p : real -> real) : term86 n c p.
Proof. exact (fun a : nat -> real => @lem7567504 n a c p). Qed.
Lemma lem7567514 (c : real) (p : real -> real) : term88 c p.
Proof. exact (fun n : nat => @lem7567509 n c p). Qed.
Lemma lem7567515 (c : real) (p : real -> real) : term47 c p.
Proof. exact (EQ_MP (@lem7567364 c p) (@lem7567514 c p)). Qed.
Lemma lem7567520 (p : real -> real) : term137 p.
Proof. exact (fun c : real => @lem7567515 c p). Qed.
Lemma lem7567525 : term138.
Proof. exact (fun p : real -> real => @lem7567520 p). Qed.
