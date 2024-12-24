Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_UREC_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm307612_spec.
Require Import thm309905_spec.
Lemma lem318096 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem318097 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem318098 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem318097 A B f) (@lem318096 A B f)). Qed.
Lemma lem318099 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem318098 A B f g). Qed.
Lemma lem318100 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem318105 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term4 A lt2).
Proof. exact (EQ_MP (@lem307612 A lt2) (@lem309905 A lt2)). Qed.
Lemma lem318106 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term4 A lt2).
Proof. exact (@lem318105 A lt2). Qed.
Lemma lem318129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem318130 {A : Type'} (lt2 : type1402 A) : (term5 A lt2) = (term6 A lt2).
Proof. exact (MK_COMB (@lem318129) (@lem318106 A lt2)). Qed.
Lemma lem318187 {A B : Type'} (lt2 : type1402 A) : (term7 A B lt2) = (term7 A B lt2).
Proof. exact (eq_refl (term7 A B lt2)). Qed.
Lemma lem318188 {A B : Type'} (lt2 : type1402 A) : (term8 A B lt2) = (term9 A B lt2).
Proof. exact (MK_COMB (@lem318130 A lt2) (@lem318187 A B lt2)). Qed.
Lemma lem318191 {A B : Type'} (lt2 : type1402 A) : (term9 A B lt2) = (term8 A B lt2).
Proof. exact (SYM (@lem318188 A B lt2)). Qed.
Lemma lem318192 {A : Type'} (lt2 : type1402 A) (h1 : term4 A lt2) : term4 A lt2.
Proof. exact (h1). Qed.
Lemma lem318193 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term10 A B lt2 H) : term10 A B lt2 H.
Proof. exact (h1). Qed.
Lemma lem318194 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term11 A B f H g) : term11 A B f H g.
Proof. exact (h1). Qed.
Lemma lem318195 {A B : Type'} (H : type549 A B) (g : A -> B) (h1 : term12 A B H g) : term12 A B H g.
Proof. exact (h1). Qed.
Lemma lem318196 {A B : Type'} (H : type549 A B) (f : A -> B) (h1 : term12 A B H f) : term12 A B H f.
Proof. exact (h1). Qed.
Lemma lem318200 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem318100 A B f g) (@lem318099 A B f g)). Qed.
Lemma lem318201 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (@lem318200 A B f g). Qed.
Lemma lem318210 {A B : Type'} (f : A -> B) (g : A -> B) : (term3 A B f g) = (f = g).
Proof. exact (SYM (@lem318201 A B f g)). Qed.
Lemma lem318243 {A : Type'} (lt2 : type1402 A) (h1 : term4 A lt2) : term4 A lt2.
Proof. exact (h1). Qed.
Lemma lem318244 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term4 A lt2) : term13 A lt2 P.
Proof. exact (@lem318243 A lt2 h1 P). Qed.
Lemma lem318245 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term13 A lt2 P) = (term14 A lt2 P).
Proof. exact (eq_refl (term13 A lt2 P)). Qed.
Lemma lem318246 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term4 A lt2) : term14 A lt2 P.
Proof. exact (EQ_MP (@lem318245 A lt2 P) (@lem318244 A P lt2 h1)). Qed.
Lemma lem318247 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term15 A lt2 P) : term15 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem318248 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term15 A lt2 P) (h2 : term4 A lt2) : term16 A P.
Proof. exact (@lem318246 A P lt2 h2 (@lem318247 A lt2 P h1)). Qed.
Lemma lem318249 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term15 A lt2 P) : term17 A lt2 P.
Proof. exact (fun h0 : term4 A lt2 => @lem318248 A P lt2 h1 h0). Qed.
Lemma lem318250 {A : Type'} (lt2 : type1402 A) (h1 : term4 A lt2) : term4 A lt2.
Proof. exact (h1). Qed.
Lemma lem318251 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term15 A lt2 P) (h2 : term4 A lt2) : term16 A P.
Proof. exact (@lem318249 A lt2 P h1 (@lem318250 A lt2 h2)). Qed.
Lemma lem318252 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term4 A lt2) : term14 A lt2 P.
Proof. exact (fun h0 : term15 A lt2 P => @lem318251 A P lt2 h0 h1). Qed.
Lemma lem318253 {A : Type'} (lt2 : type1402 A) (h1 : term4 A lt2) : term4 A lt2.
Proof. exact (fun P : A -> Prop => @lem318252 A P lt2 h1). Qed.
Lemma lem318254 {A : Type'} (lt2 : type1402 A) : term18 A lt2.
Proof. exact (fun h0 : term4 A lt2 => @lem318253 A lt2 h0). Qed.
Lemma lem318255 {A : Type'} (lt2 : type1402 A) (h1 : term4 A lt2) : term4 A lt2.
Proof. exact (@lem318254 A lt2 (@lem318192 A lt2 h1)). Qed.
Lemma lem318256 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term4 A lt2) : term13 A lt2 P.
Proof. exact (@lem318255 A lt2 h1 P). Qed.
Lemma lem318257 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term13 A lt2 P) = (term14 A lt2 P).
Proof. exact (eq_refl (term13 A lt2 P)). Qed.
Lemma lem318260 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term4 A lt2) : term14 A lt2 P.
Proof. exact (EQ_MP (@lem318257 A lt2 P) (@lem318256 A P lt2 h1)). Qed.
Lemma lem318261 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term4 A lt2) : term14 A lt2 P.
Proof. exact (@lem318260 A P lt2 h1). Qed.
Lemma lem318262 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (h1 : term4 A lt2) : term19 A B lt2 f g.
Proof. exact (@lem318261 A (term20 A B f g) lt2 h1). Qed.
Lemma lem318263 {A B : Type'} (f : A -> B) (g : A -> B) (y : A) : (term21 A B f g y) = ((f y) = (g y)).
Proof. exact (eq_refl (term21 A B f g y)). Qed.
Lemma lem318264 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term22 A lt2 y x) = (term22 A lt2 y x).
Proof. exact (eq_refl (term22 A lt2 y x)). Qed.
Lemma lem318265 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (y : A) : (term23 A B lt2 x f g y) = (term24 A B lt2 x f g y).
Proof. exact (MK_COMB (@lem318264 A lt2 y x) (@lem318263 A B f g y)). Qed.
Lemma lem318266 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term25 A B lt2 x f g) = (term26 A B lt2 x f g).
Proof. exact (fun_ext (fun y : A => @lem318265 A B lt2 x f g y)). Qed.
Lemma lem318267 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem318268 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term27 A B lt2 x f g) = (term28 A B lt2 x f g).
Proof. exact (MK_COMB (@lem318267 A) (@lem318266 A B lt2 x f g)). Qed.
Lemma lem318269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem318270 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term29 A B lt2 x f g) = (term30 A B lt2 x f g).
Proof. exact (MK_COMB (@lem318269) (@lem318268 A B lt2 x f g)). Qed.
Lemma lem318271 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term21 A B f g x) = ((f x) = (g x)).
Proof. exact (eq_refl (term21 A B f g x)). Qed.
Lemma lem318272 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) (x : A) : (term31 A B lt2 f g x) = (term32 A B lt2 f g x).
Proof. exact (MK_COMB (@lem318270 A B lt2 x f g) (@lem318271 A B f g x)). Qed.
Lemma lem318273 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) : (term33 A B lt2 f g) = (term34 A B lt2 f g).
Proof. exact (fun_ext (fun x : A => @lem318272 A B lt2 f g x)). Qed.
Lemma lem318274 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem318275 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) : (term35 A B lt2 f g) = (term36 A B lt2 f g).
Proof. exact (MK_COMB (@lem318274 A) (@lem318273 A B lt2 f g)). Qed.
Lemma lem318276 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem318277 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) : (term37 A B lt2 f g) = (term38 A B lt2 f g).
Proof. exact (MK_COMB (@lem318276) (@lem318275 A B lt2 f g)). Qed.
Lemma lem318278 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term21 A B f g x) = ((f x) = (g x)).
Proof. exact (eq_refl (term21 A B f g x)). Qed.
Lemma lem318279 {A B : Type'} (f : A -> B) (g : A -> B) : (term39 A B f g) = (term20 A B f g).
Proof. exact (fun_ext (fun x : A => @lem318278 A B f g x)). Qed.
Lemma lem318280 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem318281 {A B : Type'} (f : A -> B) (g : A -> B) : (term40 A B f g) = (term3 A B f g).
Proof. exact (MK_COMB (@lem318280 A) (@lem318279 A B f g)). Qed.
Lemma lem318282 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (g : A -> B) : (term19 A B lt2 f g) = (term41 A B lt2 f g).
Proof. exact (MK_COMB (@lem318277 A B lt2 f g) (@lem318281 A B f g)). Qed.
Lemma lem318283 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (h1 : term4 A lt2) : term41 A B lt2 f g.
Proof. exact (EQ_MP (@lem318282 A B lt2 f g) (@lem318262 A B f g lt2 h1)). Qed.
Lemma lem318284 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term28 A B lt2 x f g) : term28 A B lt2 x f g.
Proof. exact (h1). Qed.
Lemma lem318290 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term10 A B lt2 H) : term42 A B lt2 H f.
Proof. exact (@lem318193 A B lt2 H h1 f). Qed.
Lemma lem318291 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) : (term42 A B lt2 H f) = (term43 A B lt2 f H).
Proof. exact (eq_refl (term42 A B lt2 H f)). Qed.
Lemma lem318292 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term10 A B lt2 H) : term43 A B lt2 f H.
Proof. exact (EQ_MP (@lem318291 A B lt2 f H) (@lem318290 A B f lt2 H h1)). Qed.
Lemma lem318293 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term10 A B lt2 H) : term44 A B lt2 f H g.
Proof. exact (@lem318292 A B f lt2 H h1 g). Qed.
Lemma lem318294 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) : (term44 A B lt2 f H g) = (term45 A B lt2 f H g).
Proof. exact (eq_refl (term44 A B lt2 f H g)). Qed.
Lemma lem318295 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term10 A B lt2 H) : term45 A B lt2 f H g.
Proof. exact (EQ_MP (@lem318294 A B lt2 f H g) (@lem318293 A B f g lt2 H h1)). Qed.
Lemma lem318296 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (H : type549 A B) (h1 : term10 A B lt2 H) : term46 A B lt2 f H g x.
Proof. exact (@lem318295 A B f g lt2 H h1 x). Qed.
Lemma lem318297 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term46 A B lt2 f H g x) = (term47 A B lt2 f H g x).
Proof. exact (eq_refl (term46 A B lt2 f H g x)). Qed.
Lemma lem318300 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (H : type549 A B) (h1 : term10 A B lt2 H) : term47 A B lt2 f H g x.
Proof. exact (EQ_MP (@lem318297 A B lt2 f H g x) (@lem318296 A B f g x lt2 H h1)). Qed.
Lemma lem318301 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (H : type549 A B) (h1 : term10 A B lt2 H) : term47 A B lt2 f H g x.
Proof. exact (@lem318300 A B f g x lt2 H h1). Qed.
Lemma lem318302 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term28 A B lt2 x f g) (h2 : term10 A B lt2 H) : (H f x) = (H g x).
Proof. exact (@lem318301 A B f g x lt2 H h2 (@lem318284 A B lt2 x f g h1)). Qed.
Lemma lem318319 {A B : Type'} (x : A) (H : type549 A B) (f : A -> B) (h1 : term12 A B H f) : term48 A B H f x.
Proof. exact (@lem318196 A B H f h1 x). Qed.
Lemma lem318320 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (term48 A B H f x) = ((f x) = (H f x)).
Proof. exact (eq_refl (term48 A B H f x)). Qed.
Lemma lem318322 {A B : Type'} (x : A) (H : type549 A B) (g : A -> B) (h1 : term12 A B H g) : term48 A B H g x.
Proof. exact (@lem318195 A B H g h1 x). Qed.
Lemma lem318323 {A B : Type'} (H : type549 A B) (g : A -> B) (x : A) : (term48 A B H g x) = ((g x) = (H g x)).
Proof. exact (eq_refl (term48 A B H g x)). Qed.
Lemma lem318334 {A B : Type'} (x : A) (H : type549 A B) (f : A -> B) (h1 : term12 A B H f) : (f x) = (H f x).
Proof. exact (EQ_MP (@lem318320 A B H f x) (@lem318319 A B x H f h1)). Qed.
Lemma lem318335 {A B : Type'} (x : A) (H : type549 A B) (f : A -> B) (h1 : term12 A B H f) : (f x) = (H f x).
Proof. exact (@lem318334 A B x H f h1). Qed.
Lemma lem318336 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem318337 {A B : Type'} (x : A) (H : type549 A B) (f : A -> B) (h1 : term12 A B H f) : (term49 A B f x) = (term50 A B H f x).
Proof. exact (MK_COMB (@lem318336 B) (@lem318335 A B x H f h1)). Qed.
Lemma lem318339 {A B : Type'} (x : A) (H : type549 A B) (g : A -> B) (h1 : term12 A B H g) : (g x) = (H g x).
Proof. exact (EQ_MP (@lem318323 A B H g x) (@lem318322 A B x H g h1)). Qed.
Lemma lem318340 {A B : Type'} (x : A) (H : type549 A B) (g : A -> B) (h1 : term12 A B H g) : (g x) = (H g x).
Proof. exact (@lem318339 A B x H g h1). Qed.
Lemma lem318341 {A B : Type'} (x : A) (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term12 A B H f) (h2 : term12 A B H g) : ((f x) = (g x)) = ((H f x) = (H g x)).
Proof. exact (MK_COMB (@lem318337 A B x H f h1) (@lem318340 A B x H g h2)). Qed.
Lemma lem318344 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term51 A B f H g x) = (term51 A B f H g x).
Proof. exact (eq_refl (term51 A B f H g x)). Qed.
Lemma lem318345 {A B : Type'} (x : A) (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term12 A B H f) (h2 : term12 A B H g) : (term52 A B H f g x) = (term53 A B f H g x).
Proof. exact (MK_COMB (@lem318344 A B f H g x) (@lem318341 A B x f H g h1 h2)). Qed.
Lemma lem318349 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem318350 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (x : A) : (term53 A B f H g x) = True.
Proof. exact (@lem318349 ((H f x) = (H g x))). Qed.
Lemma lem318351 {A B : Type'} (x : A) (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term12 A B H f) (h2 : term12 A B H g) : (term52 A B H f g x) = True.
Proof. exact (TRANS (@lem318345 A B x f H g h1 h2) (@lem318350 A B f H g x)). Qed.
Lemma lem318352 {A B : Type'} (x : A) (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term12 A B H f) (h2 : term12 A B H g) : True = (term52 A B H f g x).
Proof. exact (SYM (@lem318351 A B x f H g h1 h2)). Qed.
Lemma lem318353 {A B : Type'} (x : A) (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term12 A B H f) (h2 : term12 A B H g) : term52 A B H f g x.
Proof. exact (EQ_MP (@lem318352 A B x f H g h1 h2) (@lem0)). Qed.
Lemma lem318354 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term12 A B H f) (h2 : term12 A B H g) (h3 : term28 A B lt2 x f g) (h4 : term10 A B lt2 H) : (f x) = (g x).
Proof. exact (@lem318353 A B x f H g h1 h2 (@lem318302 A B x f g lt2 H h3 h4)). Qed.
Lemma lem318355 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term12 A B H f) (h2 : term12 A B H g) (h3 : term10 A B lt2 H) : term32 A B lt2 f g x.
Proof. exact (fun h0 : term28 A B lt2 x f g => @lem318354 A B x f g lt2 H h1 h2 h0 h3). Qed.
Lemma lem318360 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (H : type549 A B) (h1 : term12 A B H f) (h2 : term12 A B H g) (h3 : term10 A B lt2 H) : term36 A B lt2 f g.
Proof. exact (fun x : A => @lem318355 A B x f g lt2 H h1 h2 h3). Qed.
Lemma lem318361 {A B : Type'} (f : A -> B) (g : A -> B) (H : type549 A B) (lt2 : type1402 A) (h1 : term12 A B H f) (h2 : term12 A B H g) (h3 : term10 A B lt2 H) (h4 : term4 A lt2) : term3 A B f g.
Proof. exact (@lem318283 A B f g lt2 h4 (@lem318360 A B f g lt2 H h1 h2 h3)). Qed.
Lemma lem318362 {A B : Type'} (f : A -> B) (g : A -> B) (H : type549 A B) (lt2 : type1402 A) (h1 : term12 A B H f) (h2 : term12 A B H g) (h3 : term10 A B lt2 H) (h4 : term4 A lt2) : f = g.
Proof. exact (EQ_MP (@lem318210 A B f g) (@lem318361 A B f g H lt2 h1 h2 h3 h4)). Qed.
Lemma lem318363 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term11 A B f H g) : term12 A B H g.
Proof. exact (proj2 (@lem318194 A B f H g h1)). Qed.
Lemma lem318364 {A B : Type'} (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term11 A B f H g) : term12 A B H f.
Proof. exact (proj1 (@lem318194 A B f H g h1)). Qed.
Lemma lem318365 {A B : Type'} (f : A -> B) (g : A -> B) (H : type549 A B) (lt2 : type1402 A) (h1 : term12 A B H f) (h2 : term12 A B H g) (h3 : term10 A B lt2 H) (h4 : term4 A lt2) : (term12 A B H g) = (f = g).
Proof. exact (prop_ext (fun h5 : term12 A B H g => @lem318362 A B f g H lt2 h1 h2 h3 h4) (fun h5 : f = g => @lem318195 A B H g h2)). Qed.
Lemma lem318366 {A B : Type'} (f : A -> B) (g : A -> B) (H : type549 A B) (lt2 : type1402 A) (h1 : term12 A B H f) (h2 : term12 A B H g) (h3 : term10 A B lt2 H) (h4 : term4 A lt2) : f = g.
Proof. exact (EQ_MP (@lem318365 A B f g H lt2 h1 h2 h3 h4) (@lem318195 A B H g h2)). Qed.
Lemma lem318367 {A B : Type'} (f : A -> B) (g : A -> B) (H : type549 A B) (lt2 : type1402 A) (h1 : term12 A B H f) (h2 : term12 A B H g) (h3 : term10 A B lt2 H) (h4 : term4 A lt2) : (term12 A B H f) = (f = g).
Proof. exact (prop_ext (fun h5 : term12 A B H f => @lem318366 A B f g H lt2 h1 h2 h3 h4) (fun h5 : f = g => @lem318196 A B H f h1)). Qed.
Lemma lem318368 {A B : Type'} (f : A -> B) (g : A -> B) (H : type549 A B) (lt2 : type1402 A) (h1 : term12 A B H f) (h2 : term12 A B H g) (h3 : term10 A B lt2 H) (h4 : term4 A lt2) : f = g.
Proof. exact (EQ_MP (@lem318367 A B f g H lt2 h1 h2 h3 h4) (@lem318196 A B H f h1)). Qed.
Lemma lem318369 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term12 A B H f) (h2 : term10 A B lt2 H) (h3 : term4 A lt2) (h4 : term11 A B f H g) : (term12 A B H g) = (f = g).
Proof. exact (prop_ext (fun h5 : term12 A B H g => @lem318368 A B f g H lt2 h1 h5 h2 h3) (fun h5 : f = g => @lem318363 A B f H g h4)). Qed.
Lemma lem318370 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term12 A B H f) (h2 : term10 A B lt2 H) (h3 : term4 A lt2) (h4 : term11 A B f H g) : f = g.
Proof. exact (EQ_MP (@lem318369 A B lt2 f H g h1 h2 h3 h4) (@lem318363 A B f H g h4)). Qed.
Lemma lem318371 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term10 A B lt2 H) (h2 : term4 A lt2) (h3 : term11 A B f H g) : (term12 A B H f) = (f = g).
Proof. exact (prop_ext (fun h4 : term12 A B H f => @lem318370 A B lt2 f H g h4 h1 h2 h3) (fun h4 : f = g => @lem318364 A B f H g h3)). Qed.
Lemma lem318372 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (H : type549 A B) (g : A -> B) (h1 : term10 A B lt2 H) (h2 : term4 A lt2) (h3 : term11 A B f H g) : f = g.
Proof. exact (EQ_MP (@lem318371 A B lt2 f H g h1 h2 h3) (@lem318364 A B f H g h3)). Qed.
Lemma lem318373 {A B : Type'} (f : A -> B) (g : A -> B) (H : type549 A B) (lt2 : type1402 A) (h1 : term10 A B lt2 H) (h2 : term4 A lt2) : term54 A B H f g.
Proof. exact (fun h0 : term11 A B f H g => @lem318372 A B lt2 f H g h1 h2 h0). Qed.
Lemma lem318378 {A B : Type'} (f : A -> B) (H : type549 A B) (lt2 : type1402 A) (h1 : term10 A B lt2 H) (h2 : term4 A lt2) : term55 A B H f.
Proof. exact (fun g : A -> B => @lem318373 A B f g H lt2 h1 h2). Qed.
Lemma lem318383 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term10 A B lt2 H) (h2 : term4 A lt2) : term56 A B H.
Proof. exact (fun f : A -> B => @lem318378 A B f H lt2 h1 h2). Qed.
Lemma lem318384 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term10 A B lt2 H) (h2 : term4 A lt2) : (term10 A B lt2 H) = (term56 A B H).
Proof. exact (prop_ext (fun h3 : term10 A B lt2 H => @lem318383 A B H lt2 h1 h2) (fun h3 : term56 A B H => @lem318193 A B lt2 H h1)). Qed.
Lemma lem318385 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term10 A B lt2 H) (h2 : term4 A lt2) : term56 A B H.
Proof. exact (EQ_MP (@lem318384 A B H lt2 h1 h2) (@lem318193 A B lt2 H h1)). Qed.
Lemma lem318386 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term4 A lt2) : term57 A B lt2 H.
Proof. exact (fun h0 : term10 A B lt2 H => @lem318385 A B H lt2 h0 h1). Qed.
Lemma lem318391 {A B : Type'} (lt2 : type1402 A) (h1 : term4 A lt2) : term7 A B lt2.
Proof. exact (fun H : type549 A B => @lem318386 A B H lt2 h1). Qed.
Lemma lem318392 {A B : Type'} (lt2 : type1402 A) (h1 : term4 A lt2) : (term4 A lt2) = (term7 A B lt2).
Proof. exact (prop_ext (fun h2 : term4 A lt2 => @lem318391 A B lt2 h1) (fun h2 : term7 A B lt2 => @lem318192 A lt2 h1)). Qed.
Lemma lem318393 {A B : Type'} (lt2 : type1402 A) (h1 : term4 A lt2) : term7 A B lt2.
Proof. exact (EQ_MP (@lem318392 A B lt2 h1) (@lem318192 A lt2 h1)). Qed.
Lemma lem318394 {A B : Type'} (lt2 : type1402 A) : term9 A B lt2.
Proof. exact (fun h0 : term4 A lt2 => @lem318393 A B lt2 h0). Qed.
Lemma lem318395 {A B : Type'} (lt2 : type1402 A) : term8 A B lt2.
Proof. exact (EQ_MP (@lem318191 A B lt2) (@lem318394 A B lt2)). Qed.
