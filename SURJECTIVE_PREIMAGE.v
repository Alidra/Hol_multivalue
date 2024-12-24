Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_PREIMAGE_term_abbrevs.
Require Import IN_UNIV_spec.
Require Import SUBSET_UNIV_spec.
Require Import SURJECTIVE_ON_PREIMAGE_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem5056140 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3220196 A s). Qed.
Lemma lem5056141 {A : Type'} (s : A -> Prop) : (term0 A s) = (@SUBSET A s (@UNIV A)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem5056142 {A : Type'} (s : A -> Prop) : @SUBSET A s (@UNIV A).
Proof. exact (EQ_MP (@lem5056141 A s) (@lem5056140 A s)). Qed.
Lemma lem5056143 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = ((@SUBSET A s (@UNIV A)) = True).
Proof. exact (@lem7 (@SUBSET A s (@UNIV A))). Qed.
Lemma lem5056145 {A : Type'} (x : A) : term1 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem5056146 {A : Type'} (x : A) : (term1 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem5056147 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem5056146 A x) (@lem5056145 A x)). Qed.
Lemma lem5056148 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem5056150 {A B : Type'} : term2 A B.
Proof. exact (@lem5055298 A B). Qed.
Lemma lem5056151 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (@lem5056150 A B f). Qed.
Lemma lem5056152 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (eq_refl (term3 A B f)). Qed.
Lemma lem5056153 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem5056152 A B f) (@lem5056151 A B f)). Qed.
Lemma lem5056154 {A B : Type'} (f : A -> B) : term5 A B f.
Proof. exact (@lem5056153 A B f (@UNIV A)). Qed.
Lemma lem5056155 {A B : Type'} (f : A -> B) : (term5 A B f) = (term6 A B f).
Proof. exact (eq_refl (term5 A B f)). Qed.
Lemma lem5056156 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (EQ_MP (@lem5056155 A B f) (@lem5056154 A B f)). Qed.
Lemma lem5056157 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (@lem5056156 A B f (@UNIV B)). Qed.
Lemma lem5056158 {A B : Type'} (f : A -> B) : (term7 A B f) = ((term8 A B f) = (term9 A B f)).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem5056159 {A B : Type'} (f : A -> B) : (term8 A B f) = (term9 A B f).
Proof. exact (EQ_MP (@lem5056158 A B f) (@lem5056157 A B f)). Qed.
Lemma lem5056173 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5056143 A s) (@lem5056142 A s)). Qed.
Lemma lem5056174 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (@lem5056173 A s). Qed.
Lemma lem5056175 {A : Type'} (k : A -> Prop) : (@SUBSET A k (@UNIV A)) = True.
Proof. exact (@lem5056174 A k). Qed.
Lemma lem5056176 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056177 {A : Type'} (k : A -> Prop) : (term10 A k) = (imp True).
Proof. exact (MK_COMB (@lem5056176) (@lem5056175 A k)). Qed.
Lemma lem5056185 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5056143 A s) (@lem5056142 A s)). Qed.
Lemma lem5056186 {B : Type'} (s : B -> Prop) : (@SUBSET B s (@UNIV B)) = True.
Proof. exact (@lem5056185 B s). Qed.
Lemma lem5056187 {B : Type'} (t : B -> Prop) : (@SUBSET B t (@UNIV B)) = True.
Proof. exact (@lem5056186 B t). Qed.
Lemma lem5056188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5056189 {B : Type'} (t : B -> Prop) : (term11 B t) = (and True).
Proof. exact (MK_COMB (@lem5056188) (@lem5056187 B t)). Qed.
Lemma lem5056199 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5056148 A x) (@lem5056147 A x)). Qed.
Lemma lem5056200 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem5056199 A x). Qed.
Lemma lem5056201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5056202 {A : Type'} (x : A) : (term12 A x) = (and True).
Proof. exact (MK_COMB (@lem5056201) (@lem5056200 A x)). Qed.
Lemma lem5056203 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term13 A B f x t) = (term13 A B f x t).
Proof. exact (eq_refl (term13 A B f x t)). Qed.
Lemma lem5056204 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term14 A B f x t) = (term15 A B f x t).
Proof. exact (MK_COMB (@lem5056202 A x) (@lem5056203 A B f x t)). Qed.
Lemma lem5056206 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5056207 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term15 A B f x t) = (term13 A B f x t).
Proof. exact (@lem5056206 (term13 A B f x t)). Qed.
Lemma lem5056208 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term14 A B f x t) = (term13 A B f x t).
Proof. exact (TRANS (@lem5056204 A B f x t) (@lem5056207 A B f x t)). Qed.
Lemma lem5056209 {A : Type'} (GEN_PVAR_222 : A) : (@SETSPEC A GEN_PVAR_222) = (@SETSPEC A GEN_PVAR_222).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_222)). Qed.
Lemma lem5056210 {A B : Type'} (GEN_PVAR_222 : A) (f : A -> B) (x : A) (t : B -> Prop) : (term16 A B GEN_PVAR_222 f x t) = (term17 A B GEN_PVAR_222 f x t).
Proof. exact (MK_COMB (@lem5056209 A GEN_PVAR_222) (@lem5056208 A B f x t)). Qed.
Lemma lem5056211 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5056212 {A B : Type'} (GEN_PVAR_222 : A) (f : A -> B) (t : B -> Prop) (x : A) : (term18 A B GEN_PVAR_222 f t x) = (term19 A B GEN_PVAR_222 f t x).
Proof. exact (MK_COMB (@lem5056210 A B GEN_PVAR_222 f x t) (@lem5056211 A x)). Qed.
Lemma lem5056213 {A B : Type'} (GEN_PVAR_222 : A) (f : A -> B) (t : B -> Prop) : (term20 A B GEN_PVAR_222 f t) = (term21 A B GEN_PVAR_222 f t).
Proof. exact (fun_ext (fun x : A => @lem5056212 A B GEN_PVAR_222 f t x)). Qed.
Lemma lem5056214 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5056215 {A B : Type'} (GEN_PVAR_222 : A) (f : A -> B) (t : B -> Prop) : (term22 A B GEN_PVAR_222 f t) = (term23 A B GEN_PVAR_222 f t).
Proof. exact (MK_COMB (@lem5056214 A) (@lem5056213 A B GEN_PVAR_222 f t)). Qed.
Lemma lem5056220 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term24 A B f t) = (term25 A B f t).
Proof. exact (fun_ext (fun GEN_PVAR_222 : A => @lem5056215 A B GEN_PVAR_222 f t)). Qed.
Lemma lem5056221 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5056222 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term26 A B f t) = (term27 A B f t).
Proof. exact (MK_COMB (@lem5056221 A) (@lem5056220 A B f t)). Qed.
Lemma lem5056223 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem5056224 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term28 A B f t) = (term29 A B f t).
Proof. exact (MK_COMB (@lem5056223 A) (@lem5056222 A B f t)). Qed.
Lemma lem5056225 {A : Type'} (k : A -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5056226 {A B : Type'} (f : A -> B) (t : B -> Prop) (k : A -> Prop) : ((term26 A B f t) = k) = ((term27 A B f t) = k).
Proof. exact (MK_COMB (@lem5056224 A B f t) (@lem5056225 A k)). Qed.
Lemma lem5056229 {A B : Type'} (f : A -> B) (t : B -> Prop) (k : A -> Prop) : (term30 A B f t k) = (term31 A B f t k).
Proof. exact (MK_COMB (@lem5056189 B t) (@lem5056226 A B f t k)). Qed.
Lemma lem5056231 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5056232 {A B : Type'} (f : A -> B) (t : B -> Prop) (k : A -> Prop) : (term31 A B f t k) = ((term27 A B f t) = k).
Proof. exact (@lem5056231 ((term27 A B f t) = k)). Qed.
Lemma lem5056239 {A B : Type'} (f : A -> B) (t : B -> Prop) (k : A -> Prop) : (term30 A B f t k) = ((term27 A B f t) = k).
Proof. exact (TRANS (@lem5056229 A B f t k) (@lem5056232 A B f t k)). Qed.
Lemma lem5056240 {A B : Type'} (f : A -> B) (k : A -> Prop) : (term32 A B f k) = (term33 A B f k).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5056239 A B f t k)). Qed.
Lemma lem5056241 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5056242 {A B : Type'} (f : A -> B) (k : A -> Prop) : (term34 A B f k) = (term35 A B f k).
Proof. exact (MK_COMB (@lem5056241 B) (@lem5056240 A B f k)). Qed.
Lemma lem5056247 {A B : Type'} (f : A -> B) (k : A -> Prop) : (term36 A B f k) = (term37 A B f k).
Proof. exact (MK_COMB (@lem5056177 A k) (@lem5056242 A B f k)). Qed.
Lemma lem5056249 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5056250 {A B : Type'} (f : A -> B) (k : A -> Prop) : (term37 A B f k) = (term35 A B f k).
Proof. exact (@lem5056249 (term35 A B f k)). Qed.
Lemma lem5056261 {A B : Type'} (f : A -> B) (k : A -> Prop) : (term36 A B f k) = (term35 A B f k).
Proof. exact (TRANS (@lem5056247 A B f k) (@lem5056250 A B f k)). Qed.
Lemma lem5056262 {A B : Type'} (f : A -> B) : (term38 A B f) = (term39 A B f).
Proof. exact (fun_ext (fun k : A -> Prop => @lem5056261 A B f k)). Qed.
Lemma lem5056263 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5056264 {A B : Type'} (f : A -> B) : (term8 A B f) = (term40 A B f).
Proof. exact (MK_COMB (@lem5056263 A) (@lem5056262 A B f)). Qed.
Lemma lem5056269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5056270 {A B : Type'} (f : A -> B) : (term41 A B f) = (term42 A B f).
Proof. exact (MK_COMB (@lem5056269) (@lem5056264 A B f)). Qed.
Lemma lem5056274 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5056143 A s) (@lem5056142 A s)). Qed.
Lemma lem5056275 {B : Type'} (s : B -> Prop) : (@SUBSET B s (@UNIV B)) = True.
Proof. exact (@lem5056274 B s). Qed.
Lemma lem5056276 {A B : Type'} (f : A -> B) : (term43 A B f) = True.
Proof. exact (@lem5056275 B (@IMAGE A B f (@UNIV A))). Qed.
Lemma lem5056277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5056278 {A B : Type'} (f : A -> B) : (term44 A B f) = (and True).
Proof. exact (MK_COMB (@lem5056277) (@lem5056276 A B f)). Qed.
Lemma lem5056292 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5056148 A x) (@lem5056147 A x)). Qed.
Lemma lem5056293 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem5056292 A x). Qed.
Lemma lem5056294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5056295 {A : Type'} (x : A) : (term12 A x) = (and True).
Proof. exact (MK_COMB (@lem5056294) (@lem5056293 A x)). Qed.
Lemma lem5056299 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5056148 A x) (@lem5056147 A x)). Qed.
Lemma lem5056300 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem5056299 A x). Qed.
Lemma lem5056301 {A : Type'} (y : A) : (@IN A y (@UNIV A)) = True.
Proof. exact (@lem5056300 A y). Qed.
Lemma lem5056302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5056303 {A : Type'} (y : A) : (term12 A y) = (and True).
Proof. exact (MK_COMB (@lem5056302) (@lem5056301 A y)). Qed.
Lemma lem5056306 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem5056307 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term45 A B x f y) = (term46 A B x f y).
Proof. exact (MK_COMB (@lem5056303 A y) (@lem5056306 A B x f y)). Qed.
Lemma lem5056309 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5056310 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term46 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem5056309 ((f x) = (f y))). Qed.
Lemma lem5056313 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term45 A B x f y) = ((f x) = (f y)).
Proof. exact (TRANS (@lem5056307 A B x f y) (@lem5056310 A B x f y)). Qed.
Lemma lem5056314 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term47 A B x f y) = (term46 A B x f y).
Proof. exact (MK_COMB (@lem5056295 A x) (@lem5056313 A B x f y)). Qed.
Lemma lem5056316 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5056317 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term46 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem5056316 ((f x) = (f y))). Qed.
Lemma lem5056320 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term47 A B x f y) = ((f x) = (f y)).
Proof. exact (TRANS (@lem5056314 A B x f y) (@lem5056317 A B x f y)). Qed.
Lemma lem5056321 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056322 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term48 A B x f y) = (term49 A B x f y).
Proof. exact (MK_COMB (@lem5056321) (@lem5056320 A B x f y)). Qed.
Lemma lem5056325 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5056326 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term50 A B f x y) = (term51 A B f x y).
Proof. exact (MK_COMB (@lem5056322 A B x f y) (@lem5056325 A x y)). Qed.
Lemma lem5056331 {A B : Type'} (f : A -> B) (x : A) : (term52 A B f x) = (term53 A B f x).
Proof. exact (fun_ext (fun y : A => @lem5056326 A B f x y)). Qed.
Lemma lem5056332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5056333 {A B : Type'} (f : A -> B) (x : A) : (term54 A B f x) = (term55 A B f x).
Proof. exact (MK_COMB (@lem5056332 A) (@lem5056331 A B f x)). Qed.
Lemma lem5056338 {A B : Type'} (f : A -> B) : (term56 A B f) = (term57 A B f).
Proof. exact (fun_ext (fun x : A => @lem5056333 A B f x)). Qed.
Lemma lem5056339 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5056340 {A B : Type'} (f : A -> B) : (term58 A B f) = (term59 A B f).
Proof. exact (MK_COMB (@lem5056339 A) (@lem5056338 A B f)). Qed.
Lemma lem5056345 {A B : Type'} (f : A -> B) : (term9 A B f) = (term60 A B f).
Proof. exact (MK_COMB (@lem5056278 A B f) (@lem5056340 A B f)). Qed.
Lemma lem5056347 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5056348 {A B : Type'} (f : A -> B) : (term60 A B f) = (term59 A B f).
Proof. exact (@lem5056347 (term59 A B f)). Qed.
Lemma lem5056365 {A B : Type'} (f : A -> B) : (term9 A B f) = (term59 A B f).
Proof. exact (TRANS (@lem5056345 A B f) (@lem5056348 A B f)). Qed.
Lemma lem5056366 {A B : Type'} (f : A -> B) : ((term8 A B f) = (term9 A B f)) = ((term40 A B f) = (term59 A B f)).
Proof. exact (MK_COMB (@lem5056270 A B f) (@lem5056365 A B f)). Qed.
Lemma lem5056369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056370 {A B : Type'} (f : A -> B) : (term61 A B f) = (term62 A B f).
Proof. exact (MK_COMB (@lem5056369) (@lem5056366 A B f)). Qed.
Lemma lem5056403 {A B : Type'} (f : A -> B) : ((term40 A B f) = (term59 A B f)) = ((term40 A B f) = (term59 A B f)).
Proof. exact (eq_refl ((term40 A B f) = (term59 A B f))). Qed.
Lemma lem5056404 {A B : Type'} (f : A -> B) : (term63 A B f) = (term64 A B f).
Proof. exact (MK_COMB (@lem5056370 A B f) (@lem5056403 A B f)). Qed.
Lemma lem5056408 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem5056409 {A B : Type'} (f : A -> B) : (term64 A B f) = True.
Proof. exact (@lem5056408 ((term40 A B f) = (term59 A B f))). Qed.
Lemma lem5056412 {A B : Type'} (f : A -> B) : (term65 A B f) = (term65 A B f).
Proof. exact (eq_refl (term65 A B f)). Qed.
Lemma lem5056413 {A B : Type'} (f : A -> B) : (term65 A B f) = ((term64 A B f) = True).
Proof. exact (eq_refl (term65 A B f)). Qed.
Lemma lem5056414 {A B : Type'} (f : A -> B) : (term66 A B f) = (term66 A B f).
Proof. exact (eq_refl (term66 A B f)). Qed.
Lemma lem5056415 {A B : Type'} (f : A -> B) : ((term65 A B f) = (term65 A B f)) = ((term65 A B f) = ((term64 A B f) = True)).
Proof. exact (MK_COMB (@lem5056414 A B f) (@lem5056413 A B f)). Qed.
Lemma lem5056416 {A B : Type'} (f : A -> B) : (term65 A B f) = ((term64 A B f) = True).
Proof. exact (eq_refl (term65 A B f)). Qed.
Lemma lem5056417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5056418 {A B : Type'} (f : A -> B) : (term66 A B f) = (term67 A B f).
Proof. exact (MK_COMB (@lem5056417) (@lem5056416 A B f)). Qed.
Lemma lem5056419 {A B : Type'} (f : A -> B) : ((term64 A B f) = True) = ((term64 A B f) = True).
Proof. exact (eq_refl ((term64 A B f) = True)). Qed.
Lemma lem5056420 {A B : Type'} (f : A -> B) : ((term65 A B f) = ((term64 A B f) = True)) = (((term64 A B f) = True) = ((term64 A B f) = True)).
Proof. exact (MK_COMB (@lem5056418 A B f) (@lem5056419 A B f)). Qed.
Lemma lem5056421 {A B : Type'} (f : A -> B) : ((term65 A B f) = (term65 A B f)) = (((term64 A B f) = True) = ((term64 A B f) = True)).
Proof. exact (TRANS (@lem5056415 A B f) (@lem5056420 A B f)). Qed.
Lemma lem5056422 {A B : Type'} (f : A -> B) : ((term64 A B f) = True) = ((term64 A B f) = True).
Proof. exact (EQ_MP (@lem5056421 A B f) (@lem5056412 A B f)). Qed.
Lemma lem5056423 {A B : Type'} (f : A -> B) : (term64 A B f) = True.
Proof. exact (EQ_MP (@lem5056422 A B f) (@lem5056409 A B f)). Qed.
Lemma lem5056424 {A B : Type'} (f : A -> B) : (term63 A B f) = True.
Proof. exact (TRANS (@lem5056404 A B f) (@lem5056423 A B f)). Qed.
Lemma lem5056425 {A B : Type'} (f : A -> B) : True = (term63 A B f).
Proof. exact (SYM (@lem5056424 A B f)). Qed.
Lemma lem5056426 {A B : Type'} (f : A -> B) : term63 A B f.
Proof. exact (EQ_MP (@lem5056425 A B f) (@lem0)). Qed.
Lemma lem5056427 {A B : Type'} (f : A -> B) : (term40 A B f) = (term59 A B f).
Proof. exact (@lem5056426 A B f (@lem5056159 A B f)). Qed.
Lemma lem5056432 {A B : Type'} : term68 A B.
Proof. exact (fun f : A -> B => @lem5056427 A B f). Qed.
