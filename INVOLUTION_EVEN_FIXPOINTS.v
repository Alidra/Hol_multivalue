Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INVOLUTION_EVEN_FIXPOINTS_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CARD_UNION_spec.
Require Import DISJ_ACI_spec.
Require Import EQ_TRANS_spec.
Require Import EVEN_ADD_spec.
Require Import FINITE_RESTRICT_spec.
Require Import INVOLUTION_EVEN_NOFIXPOINTS_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem4289224 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4289225 {A : Type'} (f : A -> A) (h1 : term0 A) : term1 A f.
Proof. exact (@lem4289224 A h1 f). Qed.
Lemma lem4289226 {A : Type'} (f : A -> A) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem4289227 {A : Type'} (f : A -> A) (h1 : term0 A) : term2 A f.
Proof. exact (EQ_MP (@lem4289226 A f) (@lem4289225 A f h1)). Qed.
Lemma lem4289228 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term0 A) : term3 A f s.
Proof. exact (@lem4289227 A f h1 s). Qed.
Lemma lem4289229 {A : Type'} (f : A -> A) (s : A -> Prop) : (term3 A f s) = (term4 A f s).
Proof. exact (eq_refl (term3 A f s)). Qed.
Lemma lem4289230 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term0 A) : term4 A f s.
Proof. exact (EQ_MP (@lem4289229 A f s) (@lem4289228 A f s h1)). Qed.
Lemma lem4289231 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term5 A s f) : term5 A s f.
Proof. exact (h1). Qed.
Lemma lem4289232 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term0 A) (h2 : term5 A s f) : term6 A s.
Proof. exact (@lem4289230 A f s h1 (@lem4289231 A s f h2)). Qed.
Lemma lem4289233 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term5 A s f) : term7 A s.
Proof. exact (fun h0 : term0 A => @lem4289232 A s f h0 h1). Qed.
Lemma lem4289234 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : term8 A s.
Proof. exact (h1). Qed.
Lemma lem4289235 {A : Type'} (s : A -> Prop) (h1 : term8 A s) : term7 A s.
Proof. exact (ex_elim (@lem4289234 A s h1) (fun f : A -> A => fun h0 : term9 A s f => @lem4289233 A s f h0)). Qed.
Lemma lem4289236 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4289237 {A : Type'} (s : A -> Prop) (h1 : term0 A) (h2 : term8 A s) : term6 A s.
Proof. exact (@lem4289235 A s h2 (@lem4289236 A h1)). Qed.
Lemma lem4289238 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term10 A s.
Proof. exact (fun h0 : term8 A s => @lem4289237 A s h1 h0). Qed.
Lemma lem4289239 {A : Type'} (h1 : term0 A) : term11 A.
Proof. exact (fun s : A -> Prop => @lem4289238 A s h1). Qed.
Lemma lem4289240 {A : Type'} : term12 A.
Proof. exact (fun h0 : term0 A => @lem4289239 A h0). Qed.
Lemma lem4289241 {A : Type'} : term11 A.
Proof. exact (@lem4289240 A (@lem4289223 A)). Qed.
Lemma lem4289242 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem4289241 A s). Qed.
Lemma lem4289243 {A : Type'} (s : A -> Prop) : (term13 A s) = (term10 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem4289253 (p : Prop) : term14 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem4289254 (p : Prop) : (term14 p) = (term15 p).
Proof. exact (eq_refl (term14 p)). Qed.
Lemma lem4289255 (p : Prop) : term15 p.
Proof. exact (EQ_MP (@lem4289254 p) (@lem4289253 p)). Qed.
Lemma lem4289256 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem4289257 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem4289266 (q : Prop) : (term16 q) = (term16 q).
Proof. exact (eq_refl (term16 q)). Qed.
Lemma lem4289267 (q : Prop) (p : Prop) (h1 : p = True) : (term17 q p) = (term18 q).
Proof. exact (MK_COMB (@lem4289266 q) (@lem4289256 p h1)). Qed.
Lemma lem4289268 (q : Prop) : (term18 q) = ((True = (True = q)) = q).
Proof. exact (eq_refl (term18 q)). Qed.
Lemma lem4289269 (q : Prop) (p : Prop) : (term19 q p) = (term19 q p).
Proof. exact (eq_refl (term19 q p)). Qed.
Lemma lem4289270 (p : Prop) (q : Prop) : ((term17 q p) = (term18 q)) = ((term17 q p) = ((True = (True = q)) = q)).
Proof. exact (MK_COMB (@lem4289269 q p) (@lem4289268 q)). Qed.
Lemma lem4289271 (p : Prop) (q : Prop) : (term17 q p) = ((p = (p = q)) = q).
Proof. exact (eq_refl (term17 q p)). Qed.
Lemma lem4289272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4289273 (p : Prop) (q : Prop) : (term19 q p) = (term20 p q).
Proof. exact (MK_COMB (@lem4289272) (@lem4289271 p q)). Qed.
Lemma lem4289274 (q : Prop) : ((True = (True = q)) = q) = ((True = (True = q)) = q).
Proof. exact (eq_refl ((True = (True = q)) = q)). Qed.
Lemma lem4289275 (p : Prop) (q : Prop) : ((term17 q p) = ((True = (True = q)) = q)) = (((p = (p = q)) = q) = ((True = (True = q)) = q)).
Proof. exact (MK_COMB (@lem4289273 p q) (@lem4289274 q)). Qed.
Lemma lem4289276 (p : Prop) (q : Prop) : ((term17 q p) = (term18 q)) = (((p = (p = q)) = q) = ((True = (True = q)) = q)).
Proof. exact (TRANS (@lem4289270 p q) (@lem4289275 p q)). Qed.
Lemma lem4289277 (q : Prop) (p : Prop) (h1 : p = True) : ((p = (p = q)) = q) = ((True = (True = q)) = q).
Proof. exact (EQ_MP (@lem4289276 p q) (@lem4289267 q p h1)). Qed.
Lemma lem4289278 (q : Prop) (p : Prop) (h1 : p = True) : ((True = (True = q)) = q) = ((p = (p = q)) = q).
Proof. exact (SYM (@lem4289277 q p h1)). Qed.
Lemma lem4289279 (q : Prop) : (term16 q) = (term16 q).
Proof. exact (eq_refl (term16 q)). Qed.
Lemma lem4289280 (q : Prop) (p : Prop) (h1 : p = False) : (term17 q p) = (term21 q).
Proof. exact (MK_COMB (@lem4289279 q) (@lem4289257 p h1)). Qed.
Lemma lem4289281 (q : Prop) : (term21 q) = ((False = (False = q)) = q).
Proof. exact (eq_refl (term21 q)). Qed.
Lemma lem4289282 (q : Prop) (p : Prop) : (term19 q p) = (term19 q p).
Proof. exact (eq_refl (term19 q p)). Qed.
Lemma lem4289283 (p : Prop) (q : Prop) : ((term17 q p) = (term21 q)) = ((term17 q p) = ((False = (False = q)) = q)).
Proof. exact (MK_COMB (@lem4289282 q p) (@lem4289281 q)). Qed.
Lemma lem4289284 (p : Prop) (q : Prop) : (term17 q p) = ((p = (p = q)) = q).
Proof. exact (eq_refl (term17 q p)). Qed.
Lemma lem4289285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4289286 (p : Prop) (q : Prop) : (term19 q p) = (term20 p q).
Proof. exact (MK_COMB (@lem4289285) (@lem4289284 p q)). Qed.
Lemma lem4289287 (q : Prop) : ((False = (False = q)) = q) = ((False = (False = q)) = q).
Proof. exact (eq_refl ((False = (False = q)) = q)). Qed.
Lemma lem4289288 (p : Prop) (q : Prop) : ((term17 q p) = ((False = (False = q)) = q)) = (((p = (p = q)) = q) = ((False = (False = q)) = q)).
Proof. exact (MK_COMB (@lem4289286 p q) (@lem4289287 q)). Qed.
Lemma lem4289289 (p : Prop) (q : Prop) : ((term17 q p) = (term21 q)) = (((p = (p = q)) = q) = ((False = (False = q)) = q)).
Proof. exact (TRANS (@lem4289283 p q) (@lem4289288 p q)). Qed.
Lemma lem4289290 (q : Prop) (p : Prop) (h1 : p = False) : ((p = (p = q)) = q) = ((False = (False = q)) = q).
Proof. exact (EQ_MP (@lem4289289 p q) (@lem4289280 q p h1)). Qed.
Lemma lem4289291 (q : Prop) (p : Prop) (h1 : p = False) : ((False = (False = q)) = q) = ((p = (p = q)) = q).
Proof. exact (SYM (@lem4289290 q p h1)). Qed.
Lemma lem4289295 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4289296 (q : Prop) : (True = (True = q)) = (True = q).
Proof. exact (@lem4289295 (True = q)). Qed.
Lemma lem4289298 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4289299 (q : Prop) : (True = q) = q.
Proof. exact (@lem4289298 q). Qed.
Lemma lem4289300 (q : Prop) : (True = (True = q)) = q.
Proof. exact (TRANS (@lem4289296 q) (@lem4289299 q)). Qed.
Lemma lem4289301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4289302 (q : Prop) : (term22 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem4289301) (@lem4289300 q)). Qed.
Lemma lem4289303 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem4289304 (q : Prop) : ((True = (True = q)) = q) = (q = q).
Proof. exact (MK_COMB (@lem4289302 q) (@lem4289303 q)). Qed.
Lemma lem4289306 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4289307 (x : Prop) : (x = x) = True.
Proof. exact (@lem4289306 Prop x). Qed.
Lemma lem4289308 (q : Prop) : (q = q) = True.
Proof. exact (@lem4289307 q). Qed.
Lemma lem4289309 (q : Prop) : ((True = (True = q)) = q) = True.
Proof. exact (TRANS (@lem4289304 q) (@lem4289308 q)). Qed.
Lemma lem4289310 (q : Prop) : True = ((True = (True = q)) = q).
Proof. exact (SYM (@lem4289309 q)). Qed.
Lemma lem4289311 (q : Prop) : (True = (True = q)) = q.
Proof. exact (EQ_MP (@lem4289310 q) (@lem0)). Qed.
Lemma lem4289315 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4289316 (q : Prop) : (False = (False = q)) = (term23 q).
Proof. exact (@lem4289315 (False = q)). Qed.
Lemma lem4289318 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4289319 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem4289318 q). Qed.
Lemma lem4289320 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4289321 (q : Prop) : (term23 q) = (term24 q).
Proof. exact (MK_COMB (@lem4289320) (@lem4289319 q)). Qed.
Lemma lem4289323 (t : Prop) : (term24 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem4289324 (q : Prop) : (term24 q) = q.
Proof. exact (@lem4289323 q). Qed.
Lemma lem4289325 (q : Prop) : (term23 q) = q.
Proof. exact (TRANS (@lem4289321 q) (@lem4289324 q)). Qed.
Lemma lem4289326 (q : Prop) : (False = (False = q)) = q.
Proof. exact (TRANS (@lem4289316 q) (@lem4289325 q)). Qed.
Lemma lem4289327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4289328 (q : Prop) : (term25 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem4289327) (@lem4289326 q)). Qed.
Lemma lem4289329 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem4289330 (q : Prop) : ((False = (False = q)) = q) = (q = q).
Proof. exact (MK_COMB (@lem4289328 q) (@lem4289329 q)). Qed.
Lemma lem4289332 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4289333 (x : Prop) : (x = x) = True.
Proof. exact (@lem4289332 Prop x). Qed.
Lemma lem4289334 (q : Prop) : (q = q) = True.
Proof. exact (@lem4289333 q). Qed.
Lemma lem4289335 (q : Prop) : ((False = (False = q)) = q) = True.
Proof. exact (TRANS (@lem4289330 q) (@lem4289334 q)). Qed.
Lemma lem4289336 (q : Prop) : True = ((False = (False = q)) = q).
Proof. exact (SYM (@lem4289335 q)). Qed.
Lemma lem4289337 (q : Prop) : (False = (False = q)) = q.
Proof. exact (EQ_MP (@lem4289336 q) (@lem0)). Qed.
Lemma lem4289338 (q : Prop) (p : Prop) (h1 : p = False) : (p = (p = q)) = q.
Proof. exact (EQ_MP (@lem4289291 q p h1) (@lem4289337 q)). Qed.
Lemma lem4289339 (q : Prop) (p : Prop) (h1 : p = True) : (p = (p = q)) = q.
Proof. exact (EQ_MP (@lem4289278 q p h1) (@lem4289311 q)). Qed.
Lemma lem4289356 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term26 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4289357 {_102950 : Type'} (s : _102950 -> Prop) (t : _102950 -> Prop) : (s = t) = (term26 _102950 s t).
Proof. exact (@lem4289356 _102950 s t). Qed.
Lemma lem4289358 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : ((term27 _102950 s P) = (@EMPTY _102950)) = (term28 _102950 s P).
Proof. exact (@lem4289357 _102950 (term27 _102950 s P) (@EMPTY _102950)). Qed.
Lemma lem4289379 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term28 _102950 s P) = ((term27 _102950 s P) = (@EMPTY _102950)).
Proof. exact (SYM (@lem4289358 _102950 s P)). Qed.
Lemma lem4289387 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term29 A x s t) = (term30 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem4289388 {_102950 : Type'} (s : _102950 -> Prop) (x : _102950) (t : _102950 -> Prop) : (term29 _102950 x s t) = (term30 _102950 s x t).
Proof. exact (@lem4289387 _102950 s x t). Qed.
Lemma lem4289389 {_102950 : Type'} (x : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) : (term31 _102950 x s P) = (term32 _102950 x s P).
Proof. exact (@lem4289388 _102950 (term33 _102950 s P) x (term34 _102950 s P)). Qed.
Lemma lem4289393 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4289394 {_102950 : Type'} (p : _102950 -> Prop) (x : _102950) : (term35 _102950 x p) = (p x).
Proof. exact (@lem4289393 _102950 p x). Qed.
Lemma lem4289395 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term36 _102950 x s P) = (term37 _102950 s P x).
Proof. exact (@lem4289394 _102950 (term38 _102950 s P) x). Qed.
Lemma lem4289396 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term37 _102950 s P x) = (term39 _102950 s P x).
Proof. exact (eq_refl (term37 _102950 s P x)). Qed.
Lemma lem4289397 {_102950 : Type'} (GEN_PVAR_114 : _102950) : (@SETSPEC _102950 GEN_PVAR_114) = (@SETSPEC _102950 GEN_PVAR_114).
Proof. exact (eq_refl (@SETSPEC _102950 GEN_PVAR_114)). Qed.
Lemma lem4289398 {_102950 : Type'} (GEN_PVAR_114 : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term40 _102950 GEN_PVAR_114 s P x) = (term41 _102950 GEN_PVAR_114 s P x).
Proof. exact (MK_COMB (@lem4289397 _102950 GEN_PVAR_114) (@lem4289396 _102950 s P x)). Qed.
Lemma lem4289399 {_102950 : Type'} (x : _102950) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4289400 {_102950 : Type'} (GEN_PVAR_114 : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term42 _102950 GEN_PVAR_114 s P x) = (term43 _102950 GEN_PVAR_114 s P x).
Proof. exact (MK_COMB (@lem4289398 _102950 GEN_PVAR_114 s P x) (@lem4289399 _102950 x)). Qed.
Lemma lem4289401 {_102950 : Type'} (GEN_PVAR_114 : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) : (term44 _102950 GEN_PVAR_114 s P) = (term45 _102950 GEN_PVAR_114 s P).
Proof. exact (fun_ext (fun x : _102950 => @lem4289400 _102950 GEN_PVAR_114 s P x)). Qed.
Lemma lem4289402 {_102950 : Type'} : (@ex _102950) = (@ex _102950).
Proof. exact (eq_refl (@ex _102950)). Qed.
Lemma lem4289403 {_102950 : Type'} (GEN_PVAR_114 : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) : (term46 _102950 GEN_PVAR_114 s P) = (term47 _102950 GEN_PVAR_114 s P).
Proof. exact (MK_COMB (@lem4289402 _102950) (@lem4289401 _102950 GEN_PVAR_114 s P)). Qed.
Lemma lem4289404 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term48 _102950 s P) = (term49 _102950 s P).
Proof. exact (fun_ext (fun GEN_PVAR_114 : _102950 => @lem4289403 _102950 GEN_PVAR_114 s P)). Qed.
Lemma lem4289405 {_102950 : Type'} : (@GSPEC _102950) = (@GSPEC _102950).
Proof. exact (eq_refl (@GSPEC _102950)). Qed.
Lemma lem4289406 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term50 _102950 s P) = (term33 _102950 s P).
Proof. exact (MK_COMB (@lem4289405 _102950) (@lem4289404 _102950 s P)). Qed.
Lemma lem4289407 {_102950 : Type'} (x : _102950) : (@IN _102950 x) = (@IN _102950 x).
Proof. exact (eq_refl (@IN _102950 x)). Qed.
Lemma lem4289408 {_102950 : Type'} (x : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) : (term36 _102950 x s P) = (term51 _102950 x s P).
Proof. exact (MK_COMB (@lem4289407 _102950 x) (@lem4289406 _102950 s P)). Qed.
Lemma lem4289409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4289410 {_102950 : Type'} (x : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) : (term52 _102950 x s P) = (term53 _102950 x s P).
Proof. exact (MK_COMB (@lem4289409) (@lem4289408 _102950 x s P)). Qed.
Lemma lem4289411 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term37 _102950 s P x) = (term39 _102950 s P x).
Proof. exact (eq_refl (term37 _102950 s P x)). Qed.
Lemma lem4289412 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : ((term36 _102950 x s P) = (term37 _102950 s P x)) = ((term51 _102950 x s P) = (term39 _102950 s P x)).
Proof. exact (MK_COMB (@lem4289410 _102950 x s P) (@lem4289411 _102950 s P x)). Qed.
Lemma lem4289413 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term51 _102950 x s P) = (term39 _102950 s P x).
Proof. exact (EQ_MP (@lem4289412 _102950 s P x) (@lem4289395 _102950 s P x)). Qed.
Lemma lem4289417 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4289418 {_102950 : Type'} (P : _102950 -> Prop) (x : _102950) : (@IN _102950 x P) = (P x).
Proof. exact (@lem4289417 _102950 P x). Qed.
Lemma lem4289419 {_102950 : Type'} (s : _102950 -> Prop) (x : _102950) : (@IN _102950 x s) = (s x).
Proof. exact (@lem4289418 _102950 s x). Qed.
Lemma lem4289420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4289421 {_102950 : Type'} (s : _102950 -> Prop) (x : _102950) : (term54 _102950 x s) = (term55 _102950 s x).
Proof. exact (MK_COMB (@lem4289420) (@lem4289419 _102950 s x)). Qed.
Lemma lem4289422 {_102950 : Type'} (P : _102950 -> Prop) (x : _102950) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem4289423 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term39 _102950 s P x) = (term56 _102950 s P x).
Proof. exact (MK_COMB (@lem4289421 _102950 s x) (@lem4289422 _102950 P x)). Qed.
Lemma lem4289426 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term51 _102950 x s P) = (term56 _102950 s P x).
Proof. exact (TRANS (@lem4289413 _102950 s P x) (@lem4289423 _102950 s P x)). Qed.
Lemma lem4289427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4289428 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term57 _102950 x s P) = (term58 _102950 s P x).
Proof. exact (MK_COMB (@lem4289427) (@lem4289426 _102950 s P x)). Qed.
Lemma lem4289430 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4289431 {_102950 : Type'} (p : _102950 -> Prop) (x : _102950) : (term35 _102950 x p) = (p x).
Proof. exact (@lem4289430 _102950 p x). Qed.
Lemma lem4289432 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term59 _102950 x s P) = (term60 _102950 s P x).
Proof. exact (@lem4289431 _102950 (term61 _102950 s P) x). Qed.
Lemma lem4289433 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term60 _102950 s P x) = (term62 _102950 s P x).
Proof. exact (eq_refl (term60 _102950 s P x)). Qed.
Lemma lem4289434 {_102950 : Type'} (GEN_PVAR_115 : _102950) : (@SETSPEC _102950 GEN_PVAR_115) = (@SETSPEC _102950 GEN_PVAR_115).
Proof. exact (eq_refl (@SETSPEC _102950 GEN_PVAR_115)). Qed.
Lemma lem4289435 {_102950 : Type'} (GEN_PVAR_115 : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term63 _102950 GEN_PVAR_115 s P x) = (term64 _102950 GEN_PVAR_115 s P x).
Proof. exact (MK_COMB (@lem4289434 _102950 GEN_PVAR_115) (@lem4289433 _102950 s P x)). Qed.
Lemma lem4289436 {_102950 : Type'} (x : _102950) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4289437 {_102950 : Type'} (GEN_PVAR_115 : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term65 _102950 GEN_PVAR_115 s P x) = (term66 _102950 GEN_PVAR_115 s P x).
Proof. exact (MK_COMB (@lem4289435 _102950 GEN_PVAR_115 s P x) (@lem4289436 _102950 x)). Qed.
Lemma lem4289438 {_102950 : Type'} (GEN_PVAR_115 : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) : (term67 _102950 GEN_PVAR_115 s P) = (term68 _102950 GEN_PVAR_115 s P).
Proof. exact (fun_ext (fun x : _102950 => @lem4289437 _102950 GEN_PVAR_115 s P x)). Qed.
Lemma lem4289439 {_102950 : Type'} : (@ex _102950) = (@ex _102950).
Proof. exact (eq_refl (@ex _102950)). Qed.
Lemma lem4289440 {_102950 : Type'} (GEN_PVAR_115 : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) : (term69 _102950 GEN_PVAR_115 s P) = (term70 _102950 GEN_PVAR_115 s P).
Proof. exact (MK_COMB (@lem4289439 _102950) (@lem4289438 _102950 GEN_PVAR_115 s P)). Qed.
Lemma lem4289441 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term71 _102950 s P) = (term72 _102950 s P).
Proof. exact (fun_ext (fun GEN_PVAR_115 : _102950 => @lem4289440 _102950 GEN_PVAR_115 s P)). Qed.
Lemma lem4289442 {_102950 : Type'} : (@GSPEC _102950) = (@GSPEC _102950).
Proof. exact (eq_refl (@GSPEC _102950)). Qed.
Lemma lem4289443 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term73 _102950 s P) = (term34 _102950 s P).
Proof. exact (MK_COMB (@lem4289442 _102950) (@lem4289441 _102950 s P)). Qed.
Lemma lem4289444 {_102950 : Type'} (x : _102950) : (@IN _102950 x) = (@IN _102950 x).
Proof. exact (eq_refl (@IN _102950 x)). Qed.
Lemma lem4289445 {_102950 : Type'} (x : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) : (term59 _102950 x s P) = (term74 _102950 x s P).
Proof. exact (MK_COMB (@lem4289444 _102950 x) (@lem4289443 _102950 s P)). Qed.
Lemma lem4289446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4289447 {_102950 : Type'} (x : _102950) (s : _102950 -> Prop) (P : _102950 -> Prop) : (term75 _102950 x s P) = (term76 _102950 x s P).
Proof. exact (MK_COMB (@lem4289446) (@lem4289445 _102950 x s P)). Qed.
Lemma lem4289448 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term60 _102950 s P x) = (term62 _102950 s P x).
Proof. exact (eq_refl (term60 _102950 s P x)). Qed.
Lemma lem4289449 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : ((term59 _102950 x s P) = (term60 _102950 s P x)) = ((term74 _102950 x s P) = (term62 _102950 s P x)).
Proof. exact (MK_COMB (@lem4289447 _102950 x s P) (@lem4289448 _102950 s P x)). Qed.
Lemma lem4289450 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term74 _102950 x s P) = (term62 _102950 s P x).
Proof. exact (EQ_MP (@lem4289449 _102950 s P x) (@lem4289432 _102950 s P x)). Qed.
Lemma lem4289454 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4289455 {_102950 : Type'} (P : _102950 -> Prop) (x : _102950) : (@IN _102950 x P) = (P x).
Proof. exact (@lem4289454 _102950 P x). Qed.
Lemma lem4289456 {_102950 : Type'} (s : _102950 -> Prop) (x : _102950) : (@IN _102950 x s) = (s x).
Proof. exact (@lem4289455 _102950 s x). Qed.
Lemma lem4289457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4289458 {_102950 : Type'} (s : _102950 -> Prop) (x : _102950) : (term54 _102950 x s) = (term55 _102950 s x).
Proof. exact (MK_COMB (@lem4289457) (@lem4289456 _102950 s x)). Qed.
Lemma lem4289459 {_102950 : Type'} (P : _102950 -> Prop) (x : _102950) : (term77 _102950 P x) = (term77 _102950 P x).
Proof. exact (eq_refl (term77 _102950 P x)). Qed.
Lemma lem4289460 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term62 _102950 s P x) = (term78 _102950 s P x).
Proof. exact (MK_COMB (@lem4289458 _102950 s x) (@lem4289459 _102950 P x)). Qed.
Lemma lem4289463 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term74 _102950 x s P) = (term78 _102950 s P x).
Proof. exact (TRANS (@lem4289450 _102950 s P x) (@lem4289460 _102950 s P x)). Qed.
Lemma lem4289464 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term32 _102950 x s P) = (term79 _102950 s P x).
Proof. exact (MK_COMB (@lem4289428 _102950 s P x) (@lem4289463 _102950 s P x)). Qed.
Lemma lem4289467 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term31 _102950 x s P) = (term79 _102950 s P x).
Proof. exact (TRANS (@lem4289389 _102950 x s P) (@lem4289464 _102950 s P x)). Qed.
Lemma lem4289468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4289469 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term80 _102950 x s P) = (term81 _102950 s P x).
Proof. exact (MK_COMB (@lem4289468) (@lem4289467 _102950 s P x)). Qed.
Lemma lem4289471 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4289472 {_102950 : Type'} (x : _102950) : (@IN _102950 x (@EMPTY _102950)) = False.
Proof. exact (@lem4289471 _102950 x). Qed.
Lemma lem4289473 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : ((term31 _102950 x s P) = (@IN _102950 x (@EMPTY _102950))) = ((term79 _102950 s P x) = False).
Proof. exact (MK_COMB (@lem4289469 _102950 s P x) (@lem4289472 _102950 x)). Qed.
Lemma lem4289475 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4289476 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : ((term79 _102950 s P x) = False) = (term82 _102950 s P x).
Proof. exact (@lem4289475 (term79 _102950 s P x)). Qed.
Lemma lem4289483 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : ((term31 _102950 x s P) = (@IN _102950 x (@EMPTY _102950))) = (term82 _102950 s P x).
Proof. exact (TRANS (@lem4289473 _102950 s P x) (@lem4289476 _102950 s P x)). Qed.
Lemma lem4289484 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term83 _102950 s P) = (term84 _102950 s P).
Proof. exact (fun_ext (fun x : _102950 => @lem4289483 _102950 s P x)). Qed.
Lemma lem4289485 {_102950 : Type'} : (@all _102950) = (@all _102950).
Proof. exact (eq_refl (@all _102950)). Qed.
Lemma lem4289486 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term28 _102950 s P) = (term85 _102950 s P).
Proof. exact (MK_COMB (@lem4289485 _102950) (@lem4289484 _102950 s P)). Qed.
Lemma lem4289491 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term85 _102950 s P) = (term28 _102950 s P).
Proof. exact (SYM (@lem4289486 _102950 s P)). Qed.
Lemma lem4289493 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4289494 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term85 _102950 s P) = (term87 _102950 s P).
Proof. exact (@lem4289493 (term85 _102950 s P)). Qed.
Lemma lem4289495 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term87 _102950 s P) = (term85 _102950 s P).
Proof. exact (SYM (@lem4289494 _102950 s P)). Qed.
Lemma lem4289496 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term88 _102950 s P) : term88 _102950 s P.
Proof. exact (h1). Qed.
Lemma lem4289499 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term87 _102950 s P) : term87 _102950 s P.
Proof. exact (h1). Qed.
Lemma lem4289500 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : term89 _102950 s P.
Proof. exact (fun h0 : term87 _102950 s P => @lem4289499 _102950 s P h0). Qed.
Lemma lem4289501 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term89 _102950 s P) : term89 _102950 s P.
Proof. exact (h1). Qed.
Lemma lem4289502 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term87 _102950 s P) : term87 _102950 s P.
Proof. exact (h1). Qed.
Lemma lem4289503 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term87 _102950 s P) (h2 : term89 _102950 s P) : term87 _102950 s P.
Proof. exact (@lem4289501 _102950 s P h2 (@lem4289502 _102950 s P h1)). Qed.
Lemma lem4289504 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term87 _102950 s P) : term90 _102950 s P.
Proof. exact (fun h0 : term89 _102950 s P => @lem4289503 _102950 s P h1 h0). Qed.
Lemma lem4289505 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term89 _102950 s P) : term89 _102950 s P.
Proof. exact (h1). Qed.
Lemma lem4289506 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term87 _102950 s P) (h2 : term89 _102950 s P) : term87 _102950 s P.
Proof. exact (@lem4289504 _102950 s P h1 (@lem4289505 _102950 s P h2)). Qed.
Lemma lem4289507 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term89 _102950 s P) : term89 _102950 s P.
Proof. exact (fun h0 : term87 _102950 s P => @lem4289506 _102950 s P h0 h1). Qed.
Lemma lem4289508 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : term91 _102950 s P.
Proof. exact (fun h0 : term89 _102950 s P => @lem4289507 _102950 s P h0). Qed.
Lemma lem4289511 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : term89 _102950 s P.
Proof. exact (@lem4289508 _102950 s P (@lem4289500 _102950 s P)). Qed.
Lemma lem4289512 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : term89 _102950 s P.
Proof. exact (@lem4289511 _102950 s P). Qed.
Lemma lem4289522 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4289523 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term87 _102950 s P) = (term92 _102950 s P).
Proof. exact (@lem4289522 (term88 _102950 s P)). Qed.
Lemma lem4289525 (t : Prop) : (term24 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4289526 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term92 _102950 s P) = (term85 _102950 s P).
Proof. exact (@lem4289525 (term85 _102950 s P)). Qed.
Lemma lem4289531 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term87 _102950 s P) = (term85 _102950 s P).
Proof. exact (TRANS (@lem4289523 _102950 s P) (@lem4289526 _102950 s P)). Qed.
Lemma lem4289538 {_102950 : Type'} (P : _102950 -> Prop) : (term93 _102950 P) = (term94 _102950 P).
Proof. exact (fun_ext (fun s : _102950 -> Prop => @lem4289531 _102950 s P)). Qed.
Lemma lem4289539 {_102950 : Type'} : (@all (_102950 -> Prop)) = (@all (_102950 -> Prop)).
Proof. exact (eq_refl (@all (_102950 -> Prop))). Qed.
Lemma lem4289540 {_102950 : Type'} (P : _102950 -> Prop) : (term95 _102950 P) = (term96 _102950 P).
Proof. exact (MK_COMB (@lem4289539 _102950) (@lem4289538 _102950 P)). Qed.
Lemma lem4289545 {_102950 : Type'} : (term97 _102950) = (term98 _102950).
Proof. exact (fun_ext (fun P : _102950 -> Prop => @lem4289540 _102950 P)). Qed.
Lemma lem4289546 {_102950 : Type'} : (@all (_102950 -> Prop)) = (@all (_102950 -> Prop)).
Proof. exact (eq_refl (@all (_102950 -> Prop))). Qed.
Lemma lem4289555 {_102950 : Type'} : (term99 _102950) = (term100 _102950).
Proof. exact (MK_COMB (@lem4289546 _102950) (@lem4289545 _102950)). Qed.
Lemma lem4289572 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term82 _102950 s P x) = (term82 _102950 s P x).
Proof. exact (eq_refl (term82 _102950 s P x)). Qed.
Lemma lem4289573 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term84 _102950 s P) = (term84 _102950 s P).
Proof. exact (fun_ext (fun x : _102950 => @lem4289572 _102950 s P x)). Qed.
Lemma lem4289574 {_102950 : Type'} : (@all _102950) = (@all _102950).
Proof. exact (eq_refl (@all _102950)). Qed.
Lemma lem4289575 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term85 _102950 s P) = (term85 _102950 s P).
Proof. exact (MK_COMB (@lem4289574 _102950) (@lem4289573 _102950 s P)). Qed.
Lemma lem4289576 {_102950 : Type'} (P : _102950 -> Prop) : (term94 _102950 P) = (term94 _102950 P).
Proof. exact (fun_ext (fun s : _102950 -> Prop => @lem4289575 _102950 s P)). Qed.
Lemma lem4289577 {_102950 : Type'} : (@all (_102950 -> Prop)) = (@all (_102950 -> Prop)).
Proof. exact (eq_refl (@all (_102950 -> Prop))). Qed.
Lemma lem4289578 {_102950 : Type'} (P : _102950 -> Prop) : (term96 _102950 P) = (term96 _102950 P).
Proof. exact (MK_COMB (@lem4289577 _102950) (@lem4289576 _102950 P)). Qed.
Lemma lem4289579 {_102950 : Type'} : (term98 _102950) = (term98 _102950).
Proof. exact (fun_ext (fun P : _102950 -> Prop => @lem4289578 _102950 P)). Qed.
Lemma lem4289580 {_102950 : Type'} : (@all (_102950 -> Prop)) = (@all (_102950 -> Prop)).
Proof. exact (eq_refl (@all (_102950 -> Prop))). Qed.
Lemma lem4289581 {_102950 : Type'} : (term100 _102950) = (term100 _102950).
Proof. exact (MK_COMB (@lem4289580 _102950) (@lem4289579 _102950)). Qed.
Lemma lem4289608 {_102950 : Type'} : (term99 _102950) = (term100 _102950).
Proof. exact (TRANS (@lem4289555 _102950) (@lem4289581 _102950)). Qed.
Lemma lem4289609 {_102950 : Type'} : (term100 _102950) = (term99 _102950).
Proof. exact (SYM (@lem4289608 _102950)). Qed.
Lemma lem4289628 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : term79 _102950 s P x.
Proof. exact (h1). Qed.
Lemma lem4289652 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : term79 _102950 s P x.
Proof. exact (h1). Qed.
Lemma lem4289653 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : term78 _102950 s P x.
Proof. exact (proj2 (@lem4289652 _102950 s P x h1)). Qed.
Lemma lem4289654 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : term56 _102950 s P x.
Proof. exact (proj1 (@lem4289652 _102950 s P x h1)). Qed.
Lemma lem4289678 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : term77 _102950 P x.
Proof. exact (proj2 (@lem4289653 _102950 s P x h1)). Qed.
Lemma lem4289684 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : P x.
Proof. exact (proj2 (@lem4289654 _102950 s P x h1)). Qed.
Lemma lem4289685 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : term101 _102950 P x.
Proof. exact (fun h0 : term77 _102950 P x => @lem4289684 _102950 s P x h1). Qed.
Lemma lem4289687 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4289688 {_102950 : Type'} (P : _102950 -> Prop) (x : _102950) : (term101 _102950 P x) = (P x).
Proof. exact (@lem4289687 (P x)). Qed.
Lemma lem4289689 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : P x.
Proof. exact (EQ_MP (@lem4289688 _102950 P x) (@lem4289685 _102950 s P x h1)). Qed.
Lemma lem4289692 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4289694 {_102950 : Type'} (P : _102950 -> Prop) (x : _102950) : (term77 _102950 P x) = (term103 _102950 P x).
Proof. exact (@lem4289692 (P x)). Qed.
Lemma lem4289697 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : term103 _102950 P x.
Proof. exact (EQ_MP (@lem4289694 _102950 P x) (@lem4289678 _102950 s P x h1)). Qed.
Lemma lem4289700 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : False.
Proof. exact (@lem4289697 _102950 s P x h1 (@lem4289689 _102950 s P x h1)). Qed.
Lemma lem4289701 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : term104.
Proof. exact (fun h0 : ~ False => @lem4289700 _102950 s P x h1). Qed.
Lemma lem4289703 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4289704 : term104 = False.
Proof. exact (@lem4289703 False). Qed.
Lemma lem4289705 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : False.
Proof. exact (EQ_MP (@lem4289704) (@lem4289701 _102950 s P x h1)). Qed.
Lemma lem4289706 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : (term79 _102950 s P x) = False.
Proof. exact (prop_ext (fun h2 : term79 _102950 s P x => @lem4289705 _102950 s P x h1) (fun h2 : False => @lem4289652 _102950 s P x h1)). Qed.
Lemma lem4289707 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : False.
Proof. exact (EQ_MP (@lem4289706 _102950 s P x h1) (@lem4289652 _102950 s P x h1)). Qed.
Lemma lem4289708 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : (term79 _102950 s P x) = False.
Proof. exact (prop_ext (fun h2 : term79 _102950 s P x => @lem4289707 _102950 s P x h1) (fun h2 : False => @lem4289628 _102950 s P x h1)). Qed.
Lemma lem4289709 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) (h1 : term79 _102950 s P x) : False.
Proof. exact (EQ_MP (@lem4289708 _102950 s P x h1) (@lem4289628 _102950 s P x h1)). Qed.
Lemma lem4289710 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : term105 _102950 s P x.
Proof. exact (fun h0 : term79 _102950 s P x => @lem4289709 _102950 s P x h0). Qed.
Lemma lem4289711 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : (term105 _102950 s P x) = (term82 _102950 s P x).
Proof. exact (@lem69 (term79 _102950 s P x)). Qed.
Lemma lem4289712 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (x : _102950) : term82 _102950 s P x.
Proof. exact (EQ_MP (@lem4289711 _102950 s P x) (@lem4289710 _102950 s P x)). Qed.
Lemma lem4289717 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : term85 _102950 s P.
Proof. exact (fun x : _102950 => @lem4289712 _102950 s P x). Qed.
Lemma lem4289722 {_102950 : Type'} (P : _102950 -> Prop) : term96 _102950 P.
Proof. exact (fun s : _102950 -> Prop => @lem4289717 _102950 s P). Qed.
Lemma lem4289727 {_102950 : Type'} : term100 _102950.
Proof. exact (fun P : _102950 -> Prop => @lem4289722 _102950 P). Qed.
Lemma lem4289728 {_102950 : Type'} : term99 _102950.
Proof. exact (EQ_MP (@lem4289609 _102950) (@lem4289727 _102950)). Qed.
Lemma lem4289729 {_102950 : Type'} (P : _102950 -> Prop) : term106 _102950 P.
Proof. exact (@lem4289728 _102950 P). Qed.
Lemma lem4289730 {_102950 : Type'} (P : _102950 -> Prop) : (term106 _102950 P) = (term95 _102950 P).
Proof. exact (eq_refl (term106 _102950 P)). Qed.
Lemma lem4289731 {_102950 : Type'} (P : _102950 -> Prop) : term95 _102950 P.
Proof. exact (EQ_MP (@lem4289730 _102950 P) (@lem4289729 _102950 P)). Qed.
Lemma lem4289732 {_102950 : Type'} (P : _102950 -> Prop) (s : _102950 -> Prop) : term107 _102950 P s.
Proof. exact (@lem4289731 _102950 P s). Qed.
Lemma lem4289733 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term107 _102950 P s) = (term87 _102950 s P).
Proof. exact (eq_refl (term107 _102950 P s)). Qed.
Lemma lem4289734 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : term87 _102950 s P.
Proof. exact (EQ_MP (@lem4289733 _102950 s P) (@lem4289732 _102950 P s)). Qed.
Lemma lem4289736 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : term87 _102950 s P.
Proof. exact (@lem4289512 _102950 s P (@lem4289734 _102950 s P)). Qed.
Lemma lem4289737 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term88 _102950 s P) : False.
Proof. exact (@lem4289736 _102950 s P (@lem4289496 _102950 s P h1)). Qed.
Lemma lem4289738 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term88 _102950 s P) : (term88 _102950 s P) = False.
Proof. exact (prop_ext (fun h2 : term88 _102950 s P => @lem4289737 _102950 s P h1) (fun h2 : False => @lem4289496 _102950 s P h1)). Qed.
Lemma lem4289739 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) (h1 : term88 _102950 s P) : False.
Proof. exact (EQ_MP (@lem4289738 _102950 s P h1) (@lem4289496 _102950 s P h1)). Qed.
Lemma lem4289740 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : term87 _102950 s P.
Proof. exact (fun h0 : term88 _102950 s P => @lem4289739 _102950 s P h0). Qed.
Lemma lem4289741 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : term85 _102950 s P.
Proof. exact (EQ_MP (@lem4289495 _102950 s P) (@lem4289740 _102950 s P)). Qed.
Lemma lem4289742 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : term28 _102950 s P.
Proof. exact (EQ_MP (@lem4289491 _102950 s P) (@lem4289741 _102950 s P)). Qed.
Lemma lem4289754 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term108 A s f) : term108 A s f.
Proof. exact (h1). Qed.
Lemma lem4289755 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term109 A s f) : term109 A s f.
Proof. exact (h1). Qed.
Lemma lem4289756 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4289757 : term110.
Proof. exact (@lem403 Prop). Qed.
Lemma lem4289758 (h1 : term110) : term110.
Proof. exact (h1). Qed.
Lemma lem4289759 (x : Prop) (h1 : term110) : term111 x.
Proof. exact (@lem4289758 h1 x). Qed.
Lemma lem4289760 (x : Prop) : (term111 x) = (term112 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem4289761 (x : Prop) (h1 : term110) : term112 x.
Proof. exact (EQ_MP (@lem4289760 x) (@lem4289759 x h1)). Qed.
Lemma lem4289762 (x : Prop) (y : Prop) (h1 : term110) : term113 x y.
Proof. exact (@lem4289761 x h1 y). Qed.
Lemma lem4289763 (y : Prop) (x : Prop) : (term113 x y) = (term114 y x).
Proof. exact (eq_refl (term113 x y)). Qed.
Lemma lem4289764 (y : Prop) (x : Prop) (h1 : term110) : term114 y x.
Proof. exact (EQ_MP (@lem4289763 y x) (@lem4289762 x y h1)). Qed.
Lemma lem4289765 (y : Prop) (x : Prop) (z : Prop) (h1 : term110) : term115 y x z.
Proof. exact (@lem4289764 y x h1 z). Qed.
Lemma lem4289766 (y : Prop) (x : Prop) (z : Prop) : (term115 y x z) = (term116 y x z).
Proof. exact (eq_refl (term115 y x z)). Qed.
Lemma lem4289767 (y : Prop) (x : Prop) (z : Prop) (h1 : term110) : term116 y x z.
Proof. exact (EQ_MP (@lem4289766 y x z) (@lem4289765 y x z h1)). Qed.
Lemma lem4289768 (x : Prop) (y : Prop) (z : Prop) (h1 : term117 x y z) : term117 x y z.
Proof. exact (h1). Qed.
Lemma lem4289769 (x : Prop) (y : Prop) (z : Prop) (h1 : term110) (h2 : term117 x y z) : x = z.
Proof. exact (@lem4289767 y x z h1 (@lem4289768 x y z h2)). Qed.
Lemma lem4289770 (x : Prop) (y : Prop) (z : Prop) (h1 : term117 x y z) : term118 x z.
Proof. exact (fun h0 : term110 => @lem4289769 x y z h0 h1). Qed.
Lemma lem4289771 (x : Prop) (z : Prop) (h1 : term119 x z) : term119 x z.
Proof. exact (h1). Qed.
Lemma lem4289772 (x : Prop) (z : Prop) (h1 : term119 x z) : term118 x z.
Proof. exact (ex_elim (@lem4289771 x z h1) (fun y : Prop => fun h0 : term120 x z y => @lem4289770 x y z h0)). Qed.
Lemma lem4289773 (h1 : term110) : term110.
Proof. exact (h1). Qed.
Lemma lem4289774 (x : Prop) (z : Prop) (h1 : term110) (h2 : term119 x z) : x = z.
Proof. exact (@lem4289772 x z h2 (@lem4289773 h1)). Qed.
Lemma lem4289775 (x : Prop) (z : Prop) (h1 : term110) : term121 x z.
Proof. exact (fun h0 : term119 x z => @lem4289774 x z h1 h0). Qed.
Lemma lem4289776 (x : Prop) (h1 : term110) : term122 x.
Proof. exact (fun z : Prop => @lem4289775 x z h1). Qed.
Lemma lem4289777 (h1 : term110) : term123.
Proof. exact (fun x : Prop => @lem4289776 x h1). Qed.
Lemma lem4289778 : term124.
Proof. exact (fun h0 : term110 => @lem4289777 h0). Qed.
Lemma lem4289779 : term123.
Proof. exact (@lem4289778 (@lem4289757)). Qed.
Lemma lem4289780 (x : Prop) : term125 x.
Proof. exact (@lem4289779 x). Qed.
Lemma lem4289781 (x : Prop) : (term125 x) = (term122 x).
Proof. exact (eq_refl (term125 x)). Qed.
Lemma lem4289782 (x : Prop) : term122 x.
Proof. exact (EQ_MP (@lem4289781 x) (@lem4289780 x)). Qed.
Lemma lem4289783 (x : Prop) (z : Prop) : term126 x z.
Proof. exact (@lem4289782 x z). Qed.
Lemma lem4289784 (x : Prop) (z : Prop) : (term126 x z) = (term121 x z).
Proof. exact (eq_refl (term126 x z)). Qed.
Lemma lem4289787 (x : Prop) (z : Prop) : term121 x z.
Proof. exact (EQ_MP (@lem4289784 x z) (@lem4289783 x z)). Qed.
Lemma lem4289788 {A : Type'} (f : A -> A) (s : A -> Prop) : term127 A f s.
Proof. exact (@lem4289787 (term128 A s f) (term6 A s)). Qed.
Lemma lem4289789 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem4289790 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem4289794 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term26 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4289795 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term26 A s t).
Proof. exact (@lem4289794 A s t). Qed.
Lemma lem4289796 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term129 A s f) = s) = (term130 A f s).
Proof. exact (@lem4289795 A (term129 A s f) s). Qed.
Lemma lem4289825 {A : Type'} (f : A -> A) (s : A -> Prop) : (term130 A f s) = ((term129 A s f) = s).
Proof. exact (SYM (@lem4289796 A f s)). Qed.
Lemma lem4289833 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term131 A x s t) = (term132 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem4289834 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term131 A x s t) = (term132 A s x t).
Proof. exact (@lem4289833 A s x t). Qed.
Lemma lem4289835 {A : Type'} (x : A) (s : A -> Prop) (f : A -> A) : (term133 A x s f) = (term134 A x s f).
Proof. exact (@lem4289834 A (term135 A s f) x (term136 A s f)). Qed.
Lemma lem4289839 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4289840 {A : Type'} (p : A -> Prop) (x : A) : (term35 A x p) = (p x).
Proof. exact (@lem4289839 A p x). Qed.
Lemma lem4289841 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term137 A x s f) = (term138 A s f x).
Proof. exact (@lem4289840 A (term139 A s f) x). Qed.
Lemma lem4289842 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term138 A s f x) = (term140 A s f x).
Proof. exact (eq_refl (term138 A s f x)). Qed.
Lemma lem4289843 {A : Type'} (GEN_PVAR_116 : A) : (@SETSPEC A GEN_PVAR_116) = (@SETSPEC A GEN_PVAR_116).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_116)). Qed.
Lemma lem4289844 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term141 A GEN_PVAR_116 s f x) = (term142 A GEN_PVAR_116 s f x).
Proof. exact (MK_COMB (@lem4289843 A GEN_PVAR_116) (@lem4289842 A s f x)). Qed.
Lemma lem4289845 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4289846 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term143 A GEN_PVAR_116 s f x) = (term144 A GEN_PVAR_116 s f x).
Proof. exact (MK_COMB (@lem4289844 A GEN_PVAR_116 s f x) (@lem4289845 A x)). Qed.
Lemma lem4289847 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) : (term145 A GEN_PVAR_116 s f) = (term146 A GEN_PVAR_116 s f).
Proof. exact (fun_ext (fun x : A => @lem4289846 A GEN_PVAR_116 s f x)). Qed.
Lemma lem4289848 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4289849 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) : (term147 A GEN_PVAR_116 s f) = (term148 A GEN_PVAR_116 s f).
Proof. exact (MK_COMB (@lem4289848 A) (@lem4289847 A GEN_PVAR_116 s f)). Qed.
Lemma lem4289850 {A : Type'} (s : A -> Prop) (f : A -> A) : (term149 A s f) = (term150 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_116 : A => @lem4289849 A GEN_PVAR_116 s f)). Qed.
Lemma lem4289851 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4289852 {A : Type'} (s : A -> Prop) (f : A -> A) : (term151 A s f) = (term135 A s f).
Proof. exact (MK_COMB (@lem4289851 A) (@lem4289850 A s f)). Qed.
Lemma lem4289853 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4289854 {A : Type'} (x : A) (s : A -> Prop) (f : A -> A) : (term137 A x s f) = (term152 A x s f).
Proof. exact (MK_COMB (@lem4289853 A x) (@lem4289852 A s f)). Qed.
Lemma lem4289855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4289856 {A : Type'} (x : A) (s : A -> Prop) (f : A -> A) : (term153 A x s f) = (term154 A x s f).
Proof. exact (MK_COMB (@lem4289855) (@lem4289854 A x s f)). Qed.
Lemma lem4289857 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term138 A s f x) = (term140 A s f x).
Proof. exact (eq_refl (term138 A s f x)). Qed.
Lemma lem4289858 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : ((term137 A x s f) = (term138 A s f x)) = ((term152 A x s f) = (term140 A s f x)).
Proof. exact (MK_COMB (@lem4289856 A x s f) (@lem4289857 A s f x)). Qed.
Lemma lem4289859 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term152 A x s f) = (term140 A s f x).
Proof. exact (EQ_MP (@lem4289858 A s f x) (@lem4289841 A s f x)). Qed.
Lemma lem4289863 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4289864 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4289863 A P x). Qed.
Lemma lem4289865 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4289864 A s x). Qed.
Lemma lem4289866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4289867 {A : Type'} (s : A -> Prop) (x : A) : (term54 A x s) = (term55 A s x).
Proof. exact (MK_COMB (@lem4289866) (@lem4289865 A s x)). Qed.
Lemma lem4289870 {A : Type'} (f : A -> A) (x : A) : ((f x) = x) = ((f x) = x).
Proof. exact (eq_refl ((f x) = x)). Qed.
Lemma lem4289871 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term140 A s f x) = (term155 A s f x).
Proof. exact (MK_COMB (@lem4289867 A s x) (@lem4289870 A f x)). Qed.
Lemma lem4289874 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term152 A x s f) = (term155 A s f x).
Proof. exact (TRANS (@lem4289859 A s f x) (@lem4289871 A s f x)). Qed.
Lemma lem4289875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4289876 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term156 A x s f) = (term157 A s f x).
Proof. exact (MK_COMB (@lem4289875) (@lem4289874 A s f x)). Qed.
Lemma lem4289878 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4289879 {A : Type'} (p : A -> Prop) (x : A) : (term35 A x p) = (p x).
Proof. exact (@lem4289878 A p x). Qed.
Lemma lem4289880 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term158 A x s f) = (term159 A s f x).
Proof. exact (@lem4289879 A (term160 A s f) x). Qed.
Lemma lem4289881 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term159 A s f x) = (term161 A s f x).
Proof. exact (eq_refl (term159 A s f x)). Qed.
Lemma lem4289882 {A : Type'} (GEN_PVAR_117 : A) : (@SETSPEC A GEN_PVAR_117) = (@SETSPEC A GEN_PVAR_117).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_117)). Qed.
Lemma lem4289883 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term162 A GEN_PVAR_117 s f x) = (term163 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4289882 A GEN_PVAR_117) (@lem4289881 A s f x)). Qed.
Lemma lem4289884 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4289885 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term164 A GEN_PVAR_117 s f x) = (term165 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4289883 A GEN_PVAR_117 s f x) (@lem4289884 A x)). Qed.
Lemma lem4289886 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term166 A GEN_PVAR_117 s f) = (term167 A GEN_PVAR_117 s f).
Proof. exact (fun_ext (fun x : A => @lem4289885 A GEN_PVAR_117 s f x)). Qed.
Lemma lem4289887 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4289888 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term168 A GEN_PVAR_117 s f) = (term169 A GEN_PVAR_117 s f).
Proof. exact (MK_COMB (@lem4289887 A) (@lem4289886 A GEN_PVAR_117 s f)). Qed.
Lemma lem4289889 {A : Type'} (s : A -> Prop) (f : A -> A) : (term170 A s f) = (term171 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_117 : A => @lem4289888 A GEN_PVAR_117 s f)). Qed.
Lemma lem4289890 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4289891 {A : Type'} (s : A -> Prop) (f : A -> A) : (term172 A s f) = (term136 A s f).
Proof. exact (MK_COMB (@lem4289890 A) (@lem4289889 A s f)). Qed.
Lemma lem4289892 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4289893 {A : Type'} (x : A) (s : A -> Prop) (f : A -> A) : (term158 A x s f) = (term173 A x s f).
Proof. exact (MK_COMB (@lem4289892 A x) (@lem4289891 A s f)). Qed.
Lemma lem4289894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4289895 {A : Type'} (x : A) (s : A -> Prop) (f : A -> A) : (term174 A x s f) = (term175 A x s f).
Proof. exact (MK_COMB (@lem4289894) (@lem4289893 A x s f)). Qed.
Lemma lem4289896 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term159 A s f x) = (term161 A s f x).
Proof. exact (eq_refl (term159 A s f x)). Qed.
Lemma lem4289897 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : ((term158 A x s f) = (term159 A s f x)) = ((term173 A x s f) = (term161 A s f x)).
Proof. exact (MK_COMB (@lem4289895 A x s f) (@lem4289896 A s f x)). Qed.
Lemma lem4289898 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term173 A x s f) = (term161 A s f x).
Proof. exact (EQ_MP (@lem4289897 A s f x) (@lem4289880 A s f x)). Qed.
Lemma lem4289902 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4289903 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4289902 A P x). Qed.
Lemma lem4289904 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4289903 A s x). Qed.
Lemma lem4289905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4289906 {A : Type'} (s : A -> Prop) (x : A) : (term54 A x s) = (term55 A s x).
Proof. exact (MK_COMB (@lem4289905) (@lem4289904 A s x)). Qed.
Lemma lem4289909 {A : Type'} (f : A -> A) (x : A) : (term176 A f x) = (term176 A f x).
Proof. exact (eq_refl (term176 A f x)). Qed.
Lemma lem4289910 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term161 A s f x) = (term177 A s f x).
Proof. exact (MK_COMB (@lem4289906 A s x) (@lem4289909 A f x)). Qed.
Lemma lem4289913 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term173 A x s f) = (term177 A s f x).
Proof. exact (TRANS (@lem4289898 A s f x) (@lem4289910 A s f x)). Qed.
Lemma lem4289914 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term134 A x s f) = (term178 A s f x).
Proof. exact (MK_COMB (@lem4289876 A s f x) (@lem4289913 A s f x)). Qed.
Lemma lem4289917 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term133 A x s f) = (term178 A s f x).
Proof. exact (TRANS (@lem4289835 A x s f) (@lem4289914 A s f x)). Qed.
Lemma lem4289918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4289919 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term179 A x s f) = (term180 A s f x).
Proof. exact (MK_COMB (@lem4289918) (@lem4289917 A s f x)). Qed.
Lemma lem4289921 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4289922 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4289921 A P x). Qed.
Lemma lem4289923 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4289922 A s x). Qed.
Lemma lem4289924 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : ((term133 A x s f) = (@IN A x s)) = ((term178 A s f x) = (s x)).
Proof. exact (MK_COMB (@lem4289919 A s f x) (@lem4289923 A s x)). Qed.
Lemma lem4289927 {A : Type'} (f : A -> A) (s : A -> Prop) : (term181 A f s) = (term182 A f s).
Proof. exact (fun_ext (fun x : A => @lem4289924 A f s x)). Qed.
Lemma lem4289928 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4289929 {A : Type'} (f : A -> A) (s : A -> Prop) : (term130 A f s) = (term183 A f s).
Proof. exact (MK_COMB (@lem4289928 A) (@lem4289927 A f s)). Qed.
Lemma lem4289934 {A : Type'} (f : A -> A) (s : A -> Prop) : (term183 A f s) = (term130 A f s).
Proof. exact (SYM (@lem4289929 A f s)). Qed.
Lemma lem4289936 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4289937 {A : Type'} (f : A -> A) (s : A -> Prop) : (term183 A f s) = (term184 A f s).
Proof. exact (@lem4289936 (term183 A f s)). Qed.
Lemma lem4289938 {A : Type'} (f : A -> A) (s : A -> Prop) : (term184 A f s) = (term183 A f s).
Proof. exact (SYM (@lem4289937 A f s)). Qed.
Lemma lem4289939 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term185 A f s) : term185 A f s.
Proof. exact (h1). Qed.
Lemma lem4289942 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term184 A f s) : term184 A f s.
Proof. exact (h1). Qed.
Lemma lem4289943 {A : Type'} (f : A -> A) (s : A -> Prop) : term186 A f s.
Proof. exact (fun h0 : term184 A f s => @lem4289942 A f s h0). Qed.
Lemma lem4289944 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term186 A f s) : term186 A f s.
Proof. exact (h1). Qed.
Lemma lem4289945 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term184 A f s) : term184 A f s.
Proof. exact (h1). Qed.
Lemma lem4289946 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term184 A f s) (h2 : term186 A f s) : term184 A f s.
Proof. exact (@lem4289944 A f s h2 (@lem4289945 A f s h1)). Qed.
Lemma lem4289947 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term184 A f s) : term187 A f s.
Proof. exact (fun h0 : term186 A f s => @lem4289946 A f s h1 h0). Qed.
Lemma lem4289948 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term186 A f s) : term186 A f s.
Proof. exact (h1). Qed.
Lemma lem4289949 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term184 A f s) (h2 : term186 A f s) : term184 A f s.
Proof. exact (@lem4289947 A f s h1 (@lem4289948 A f s h2)). Qed.
Lemma lem4289950 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term186 A f s) : term186 A f s.
Proof. exact (fun h0 : term184 A f s => @lem4289949 A f s h0 h1). Qed.
Lemma lem4289951 {A : Type'} (f : A -> A) (s : A -> Prop) : term188 A f s.
Proof. exact (fun h0 : term186 A f s => @lem4289950 A f s h0). Qed.
Lemma lem4289954 {A : Type'} (f : A -> A) (s : A -> Prop) : term186 A f s.
Proof. exact (@lem4289951 A f s (@lem4289943 A f s)). Qed.
Lemma lem4289955 {A : Type'} (f : A -> A) (s : A -> Prop) : term186 A f s.
Proof. exact (@lem4289954 A f s). Qed.
Lemma lem4289965 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4289966 {A : Type'} (f : A -> A) (s : A -> Prop) : (term184 A f s) = (term189 A f s).
Proof. exact (@lem4289965 (term185 A f s)). Qed.
Lemma lem4289968 (t : Prop) : (term24 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4289969 {A : Type'} (f : A -> A) (s : A -> Prop) : (term189 A f s) = (term183 A f s).
Proof. exact (@lem4289968 (term183 A f s)). Qed.
Lemma lem4289974 {A : Type'} (f : A -> A) (s : A -> Prop) : (term184 A f s) = (term183 A f s).
Proof. exact (TRANS (@lem4289966 A f s) (@lem4289969 A f s)). Qed.
Lemma lem4289981 {A : Type'} (s : A -> Prop) : (term190 A s) = (term191 A s).
Proof. exact (fun_ext (fun f : A -> A => @lem4289974 A f s)). Qed.
Lemma lem4289982 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4289983 {A : Type'} (s : A -> Prop) : (term192 A s) = (term193 A s).
Proof. exact (MK_COMB (@lem4289982 A) (@lem4289981 A s)). Qed.
Lemma lem4289988 {A : Type'} : (term194 A) = (term195 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4289983 A s)). Qed.
Lemma lem4289989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4289998 {A : Type'} : (term196 A) = (term197 A).
Proof. exact (MK_COMB (@lem4289989 A) (@lem4289988 A)). Qed.
Lemma lem4290017 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : ((term178 A s f x) = (s x)) = ((term178 A s f x) = (s x)).
Proof. exact (eq_refl ((term178 A s f x) = (s x))). Qed.
Lemma lem4290018 {A : Type'} (f : A -> A) (s : A -> Prop) : (term182 A f s) = (term182 A f s).
Proof. exact (fun_ext (fun x : A => @lem4290017 A f s x)). Qed.
Lemma lem4290019 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4290020 {A : Type'} (f : A -> A) (s : A -> Prop) : (term183 A f s) = (term183 A f s).
Proof. exact (MK_COMB (@lem4290019 A) (@lem4290018 A f s)). Qed.
Lemma lem4290021 {A : Type'} (s : A -> Prop) : (term191 A s) = (term191 A s).
Proof. exact (fun_ext (fun f : A -> A => @lem4290020 A f s)). Qed.
Lemma lem4290022 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4290023 {A : Type'} (s : A -> Prop) : (term193 A s) = (term193 A s).
Proof. exact (MK_COMB (@lem4290022 A) (@lem4290021 A s)). Qed.
Lemma lem4290024 {A : Type'} : (term195 A) = (term195 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4290023 A s)). Qed.
Lemma lem4290025 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4290026 {A : Type'} : (term197 A) = (term197 A).
Proof. exact (MK_COMB (@lem4290025 A) (@lem4290024 A)). Qed.
Lemma lem4290053 {A : Type'} : (term196 A) = (term197 A).
Proof. exact (TRANS (@lem4289998 A) (@lem4290026 A)). Qed.
Lemma lem4290054 {A : Type'} : (term197 A) = (term196 A).
Proof. exact (SYM (@lem4290053 A)). Qed.
Lemma lem4290056 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4290057 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : ((term178 A s f x) = (s x)) = (term198 A f s x).
Proof. exact (@lem4290056 ((term178 A s f x) = (s x))). Qed.
Lemma lem4290058 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : (term198 A f s x) = ((term178 A s f x) = (s x)).
Proof. exact (SYM (@lem4290057 A f s x)). Qed.
Lemma lem4290059 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term199 A f s x) : term199 A f s x.
Proof. exact (h1). Qed.
Lemma lem4290068 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term200 A s f x) = (term201 A s f x).
Proof. exact (@lem17045 (s x) ((f x) = x)). Qed.
Lemma lem4290077 {A : Type'} (f : A -> A) (x : A) : (term202 A f x) = ((f x) = x).
Proof. exact (@lem16933 ((f x) = x)). Qed.
Lemma lem4290079 {A : Type'} (s : A -> Prop) (x : A) : (term203 A s x) = (term203 A s x).
Proof. exact (eq_refl (term203 A s x)). Qed.
Lemma lem4290080 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term204 A s f x) = (term205 A s f x).
Proof. exact (MK_COMB (@lem4290079 A s x) (@lem4290077 A f x)). Qed.
Lemma lem4290081 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term206 A s f x) = (term204 A s f x).
Proof. exact (@lem17045 (s x) (term176 A f x)). Qed.
Lemma lem4290082 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term206 A s f x) = (term205 A s f x).
Proof. exact (TRANS (@lem4290081 A s f x) (@lem4290080 A s f x)). Qed.
Lemma lem4290086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4290087 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term207 A s f x) = (term208 A s f x).
Proof. exact (MK_COMB (@lem4290086) (@lem4290068 A s f x)). Qed.
Lemma lem4290088 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term209 A s f x) = (term210 A s f x).
Proof. exact (MK_COMB (@lem4290087 A s f x) (@lem4290082 A s f x)). Qed.
Lemma lem4290089 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term211 A s f x) = (term209 A s f x).
Proof. exact (@lem17160 (term155 A s f x) (term177 A s f x)). Qed.
Lemma lem4290090 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term211 A s f x) = (term210 A s f x).
Proof. exact (TRANS (@lem4290089 A s f x) (@lem4290088 A s f x)). Qed.
Lemma lem4290095 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4290096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4290097 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term212 A s f x) = (term213 A s f x).
Proof. exact (MK_COMB (@lem4290096) (@lem4290090 A s f x)). Qed.
Lemma lem4290098 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : (term214 A f s x) = (term215 A f s x).
Proof. exact (MK_COMB (@lem4290097 A s f x) (@lem4290095 A s x)). Qed.
Lemma lem4290103 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : (term216 A f s x) = (term216 A f s x).
Proof. exact (eq_refl (term216 A f s x)). Qed.
Lemma lem4290104 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : (term217 A f s x) = (term218 A f s x).
Proof. exact (MK_COMB (@lem4290103 A f s x) (@lem4290098 A f s x)). Qed.
Lemma lem4290105 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : (term199 A f s x) = (term217 A f s x).
Proof. exact (@lem17646 (term178 A s f x) (s x)). Qed.
Lemma lem4290110 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : (term199 A f s x) = (term218 A f s x).
Proof. exact (TRANS (@lem4290105 A f s x) (@lem4290104 A f s x)). Qed.
Lemma lem4290195 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term199 A f s x) : term218 A f s x.
Proof. exact (EQ_MP (@lem4290110 A f s x) (@lem4290059 A f s x h1)). Qed.
Lemma lem4290196 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term219 A f s x) : term219 A f s x.
Proof. exact (h1). Qed.
Lemma lem4290197 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : term215 A f s x.
Proof. exact (h1). Qed.
Lemma lem4290199 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term219 A f s x) : term178 A s f x.
Proof. exact (proj1 (@lem4290196 A f s x h1)). Qed.
Lemma lem4290200 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term155 A s f x) : term155 A s f x.
Proof. exact (h1). Qed.
Lemma lem4290201 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term177 A s f x.
Proof. exact (h1). Qed.
Lemma lem4290207 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : term210 A s f x.
Proof. exact (proj1 (@lem4290197 A f s x h1)). Qed.
Lemma lem4290208 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : term205 A s f x.
Proof. exact (proj2 (@lem4290207 A f s x h1)). Qed.
Lemma lem4290209 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : term201 A s f x.
Proof. exact (proj1 (@lem4290207 A f s x h1)). Qed.
Lemma lem4290247 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term77 A s x.
Proof. exact (h1). Qed.
Lemma lem4290251 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term77 A s x.
Proof. exact (h1). Qed.
Lemma lem4290259 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term77 A s x.
Proof. exact (h1). Qed.
Lemma lem4290275 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term77 A s x.
Proof. exact (h1). Qed.
Lemma lem4290283 {A : Type'} (f : A -> A) (x : A) (h1 : (f x) = x) : (f x) = x.
Proof. exact (h1). Qed.
Lemma lem4290287 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) : term176 A f x.
Proof. exact (h1). Qed.
Lemma lem4290289 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term219 A f s x) : term77 A s x.
Proof. exact (proj2 (@lem4290196 A f s x h1)). Qed.
Lemma lem4290295 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term219 A f s x) : term77 A s x.
Proof. exact (proj2 (@lem4290196 A f s x h1)). Qed.
Lemma lem4290303 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term77 A s x.
Proof. exact (h1). Qed.
Lemma lem4290305 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term77 A s x.
Proof. exact (h1). Qed.
Lemma lem4290309 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term77 A s x.
Proof. exact (h1). Qed.
Lemma lem4290317 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term77 A s x.
Proof. exact (h1). Qed.
Lemma lem4290321 {A : Type'} (f : A -> A) (x : A) (h1 : (f x) = x) : (f x) = x.
Proof. exact (h1). Qed.
Lemma lem4290323 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) : term176 A f x.
Proof. exact (h1). Qed.
Lemma lem4290347 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term155 A s f x) : s x.
Proof. exact (proj1 (@lem4290200 A s f x h1)). Qed.
Lemma lem4290348 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term155 A s f x) : term101 A s x.
Proof. exact (fun h0 : term77 A s x => @lem4290347 A s f x h1). Qed.
Lemma lem4290350 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290351 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (s x).
Proof. exact (@lem4290350 (s x)). Qed.
Lemma lem4290352 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term155 A s f x) : s x.
Proof. exact (EQ_MP (@lem4290351 A s x) (@lem4290348 A s f x h1)). Qed.
Lemma lem4290355 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4290357 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term103 A s x).
Proof. exact (@lem4290355 (s x)). Qed.
Lemma lem4290360 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term219 A f s x) : term103 A s x.
Proof. exact (EQ_MP (@lem4290357 A s x) (@lem4290289 A f s x h1)). Qed.
Lemma lem4290363 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term155 A s f x) (h2 : term219 A f s x) : False.
Proof. exact (@lem4290360 A f s x h2 (@lem4290352 A s f x h1)). Qed.
Lemma lem4290364 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term155 A s f x) (h2 : term219 A f s x) : term104.
Proof. exact (fun h0 : ~ False => @lem4290363 A f s x h1 h2). Qed.
Lemma lem4290366 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290367 : term104 = False.
Proof. exact (@lem4290366 False). Qed.
Lemma lem4290368 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term155 A s f x) (h2 : term219 A f s x) : False.
Proof. exact (EQ_MP (@lem4290367) (@lem4290364 A f s x h1 h2)). Qed.
Lemma lem4290392 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : s x.
Proof. exact (proj1 (@lem4290201 A s f x h1)). Qed.
Lemma lem4290393 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term101 A s x.
Proof. exact (fun h0 : term77 A s x => @lem4290392 A s f x h1). Qed.
Lemma lem4290395 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290396 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (s x).
Proof. exact (@lem4290395 (s x)). Qed.
Lemma lem4290397 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : s x.
Proof. exact (EQ_MP (@lem4290396 A s x) (@lem4290393 A s f x h1)). Qed.
Lemma lem4290400 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4290402 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term103 A s x).
Proof. exact (@lem4290400 (s x)). Qed.
Lemma lem4290405 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term219 A f s x) : term103 A s x.
Proof. exact (EQ_MP (@lem4290402 A s x) (@lem4290295 A f s x h1)). Qed.
Lemma lem4290408 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term177 A s f x) (h2 : term219 A f s x) : False.
Proof. exact (@lem4290405 A f s x h2 (@lem4290397 A s f x h1)). Qed.
Lemma lem4290409 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term177 A s f x) (h2 : term219 A f s x) : term104.
Proof. exact (fun h0 : ~ False => @lem4290408 A f s x h1 h2). Qed.
Lemma lem4290411 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290412 : term104 = False.
Proof. exact (@lem4290411 False). Qed.
Lemma lem4290413 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term177 A s f x) (h2 : term219 A f s x) : False.
Proof. exact (EQ_MP (@lem4290412) (@lem4290409 A f s x h1 h2)). Qed.
Lemma lem4290415 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : s x.
Proof. exact (proj2 (@lem4290197 A f s x h1)). Qed.
Lemma lem4290416 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : term101 A s x.
Proof. exact (fun h0 : term77 A s x => @lem4290415 A f s x h1). Qed.
Lemma lem4290418 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290419 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (s x).
Proof. exact (@lem4290418 (s x)). Qed.
Lemma lem4290420 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : s x.
Proof. exact (EQ_MP (@lem4290419 A s x) (@lem4290416 A f s x h1)). Qed.
Lemma lem4290423 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4290425 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term103 A s x).
Proof. exact (@lem4290423 (s x)). Qed.
Lemma lem4290428 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term103 A s x.
Proof. exact (EQ_MP (@lem4290425 A s x) (@lem4290303 A s x h1)). Qed.
Lemma lem4290431 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (@lem4290428 A s x h1 (@lem4290420 A f s x h2)). Qed.
Lemma lem4290432 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : term104.
Proof. exact (fun h0 : ~ False => @lem4290431 A f s x h1 h2). Qed.
Lemma lem4290434 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290435 : term104 = False.
Proof. exact (@lem4290434 False). Qed.
Lemma lem4290436 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290435) (@lem4290432 A f s x h1 h2)). Qed.
Lemma lem4290460 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : s x.
Proof. exact (proj2 (@lem4290197 A f s x h1)). Qed.
Lemma lem4290461 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : term101 A s x.
Proof. exact (fun h0 : term77 A s x => @lem4290460 A f s x h1). Qed.
Lemma lem4290463 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290464 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (s x).
Proof. exact (@lem4290463 (s x)). Qed.
Lemma lem4290465 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : s x.
Proof. exact (EQ_MP (@lem4290464 A s x) (@lem4290461 A f s x h1)). Qed.
Lemma lem4290468 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4290470 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term103 A s x).
Proof. exact (@lem4290468 (s x)). Qed.
Lemma lem4290473 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term103 A s x.
Proof. exact (EQ_MP (@lem4290470 A s x) (@lem4290309 A s x h1)). Qed.
Lemma lem4290476 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (@lem4290473 A s x h1 (@lem4290465 A f s x h2)). Qed.
Lemma lem4290477 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : term104.
Proof. exact (fun h0 : ~ False => @lem4290476 A f s x h1 h2). Qed.
Lemma lem4290479 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290480 : term104 = False.
Proof. exact (@lem4290479 False). Qed.
Lemma lem4290481 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290480) (@lem4290477 A f s x h1 h2)). Qed.
Lemma lem4290505 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : s x.
Proof. exact (proj2 (@lem4290197 A f s x h1)). Qed.
Lemma lem4290506 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : term101 A s x.
Proof. exact (fun h0 : term77 A s x => @lem4290505 A f s x h1). Qed.
Lemma lem4290508 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290509 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (s x).
Proof. exact (@lem4290508 (s x)). Qed.
Lemma lem4290510 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : s x.
Proof. exact (EQ_MP (@lem4290509 A s x) (@lem4290506 A f s x h1)). Qed.
Lemma lem4290513 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4290515 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term103 A s x).
Proof. exact (@lem4290513 (s x)). Qed.
Lemma lem4290518 {A : Type'} (s : A -> Prop) (x : A) (h1 : term77 A s x) : term103 A s x.
Proof. exact (EQ_MP (@lem4290515 A s x) (@lem4290317 A s x h1)). Qed.
Lemma lem4290521 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (@lem4290518 A s x h1 (@lem4290510 A f s x h2)). Qed.
Lemma lem4290522 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : term104.
Proof. exact (fun h0 : ~ False => @lem4290521 A f s x h1 h2). Qed.
Lemma lem4290524 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290525 : term104 = False.
Proof. exact (@lem4290524 False). Qed.
Lemma lem4290526 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290525) (@lem4290522 A f s x h1 h2)). Qed.
Lemma lem4290550 {A : Type'} (f : A -> A) (x : A) (h1 : (f x) = x) : (f x) = x.
Proof. exact (h1). Qed.
Lemma lem4290551 {A : Type'} (f : A -> A) (x : A) (h1 : (f x) = x) : term220 A f x.
Proof. exact (fun h0 : term176 A f x => @lem4290550 A f x h1). Qed.
Lemma lem4290553 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290554 {A : Type'} (f : A -> A) (x : A) : (term220 A f x) = ((f x) = x).
Proof. exact (@lem4290553 ((f x) = x)). Qed.
Lemma lem4290555 {A : Type'} (f : A -> A) (x : A) (h1 : (f x) = x) : (f x) = x.
Proof. exact (EQ_MP (@lem4290554 A f x) (@lem4290551 A f x h1)). Qed.
Lemma lem4290558 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4290560 {A : Type'} (f : A -> A) (x : A) : (term176 A f x) = (term221 A f x).
Proof. exact (@lem4290558 ((f x) = x)). Qed.
Lemma lem4290563 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) : term221 A f x.
Proof. exact (EQ_MP (@lem4290560 A f x) (@lem4290323 A f x h1)). Qed.
Lemma lem4290566 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : False.
Proof. exact (@lem4290563 A f x h1 (@lem4290555 A f x h2)). Qed.
Lemma lem4290567 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : term104.
Proof. exact (fun h0 : ~ False => @lem4290566 A f x h1 h2). Qed.
Lemma lem4290569 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4290570 : term104 = False.
Proof. exact (@lem4290569 False). Qed.
Lemma lem4290571 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4290570) (@lem4290567 A f x h1 h2)). Qed.
Lemma lem4290572 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : (term176 A f x) = False.
Proof. exact (prop_ext (fun h3 : term176 A f x => @lem4290571 A f x h1 h2) (fun h3 : False => @lem4290323 A f x h1)). Qed.
Lemma lem4290573 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4290572 A f x h1 h2) (@lem4290323 A f x h1)). Qed.
Lemma lem4290574 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : ((f x) = x) = False.
Proof. exact (prop_ext (fun h3 : (f x) = x => @lem4290573 A f x h1 h2) (fun h3 : False => @lem4290321 A f x h2)). Qed.
Lemma lem4290575 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4290574 A f x h1 h2) (@lem4290321 A f x h2)). Qed.
Lemma lem4290576 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290526 A f s x h1 h2) (fun h3 : False => @lem4290317 A s x h1)). Qed.
Lemma lem4290577 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290576 A f s x h1 h2) (@lem4290317 A s x h1)). Qed.
Lemma lem4290578 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290481 A f s x h1 h2) (fun h3 : False => @lem4290309 A s x h1)). Qed.
Lemma lem4290579 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290578 A f s x h1 h2) (@lem4290309 A s x h1)). Qed.
Lemma lem4290580 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290436 A f s x h1 h2) (fun h3 : False => @lem4290305 A s x h1)). Qed.
Lemma lem4290581 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290580 A f s x h1 h2) (@lem4290305 A s x h1)). Qed.
Lemma lem4290582 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290581 A f s x h1 h2) (fun h3 : False => @lem4290303 A s x h1)). Qed.
Lemma lem4290583 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290582 A f s x h1 h2) (@lem4290303 A s x h1)). Qed.
Lemma lem4290584 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : (term176 A f x) = False.
Proof. exact (prop_ext (fun h3 : term176 A f x => @lem4290575 A f x h1 h2) (fun h3 : False => @lem4290287 A f x h1)). Qed.
Lemma lem4290585 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4290584 A f x h1 h2) (@lem4290287 A f x h1)). Qed.
Lemma lem4290586 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : ((f x) = x) = False.
Proof. exact (prop_ext (fun h3 : (f x) = x => @lem4290585 A f x h1 h2) (fun h3 : False => @lem4290283 A f x h2)). Qed.
Lemma lem4290587 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4290586 A f x h1 h2) (@lem4290283 A f x h2)). Qed.
Lemma lem4290588 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290577 A f s x h1 h2) (fun h3 : False => @lem4290275 A s x h1)). Qed.
Lemma lem4290589 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290588 A f s x h1 h2) (@lem4290275 A s x h1)). Qed.
Lemma lem4290590 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290579 A f s x h1 h2) (fun h3 : False => @lem4290259 A s x h1)). Qed.
Lemma lem4290591 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290590 A f s x h1 h2) (@lem4290259 A s x h1)). Qed.
Lemma lem4290592 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290583 A f s x h1 h2) (fun h3 : False => @lem4290251 A s x h1)). Qed.
Lemma lem4290593 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290592 A f s x h1 h2) (@lem4290251 A s x h1)). Qed.
Lemma lem4290594 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290593 A f s x h1 h2) (fun h3 : False => @lem4290247 A s x h1)). Qed.
Lemma lem4290595 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290594 A f s x h1 h2) (@lem4290247 A s x h1)). Qed.
Lemma lem4290596 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : (term176 A f x) = False.
Proof. exact (prop_ext (fun h3 : term176 A f x => @lem4290587 A f x h1 h2) (fun h3 : False => @lem4290287 A f x h1)). Qed.
Lemma lem4290597 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4290596 A f x h1 h2) (@lem4290287 A f x h1)). Qed.
Lemma lem4290598 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : ((f x) = x) = False.
Proof. exact (prop_ext (fun h3 : (f x) = x => @lem4290597 A f x h1 h2) (fun h3 : False => @lem4290283 A f x h2)). Qed.
Lemma lem4290599 {A : Type'} (f : A -> A) (x : A) (h1 : term176 A f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4290598 A f x h1 h2) (@lem4290283 A f x h2)). Qed.
Lemma lem4290600 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290589 A f s x h1 h2) (fun h3 : False => @lem4290275 A s x h1)). Qed.
Lemma lem4290601 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290600 A f s x h1 h2) (@lem4290275 A s x h1)). Qed.
Lemma lem4290602 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290591 A f s x h1 h2) (fun h3 : False => @lem4290259 A s x h1)). Qed.
Lemma lem4290603 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290602 A f s x h1 h2) (@lem4290259 A s x h1)). Qed.
Lemma lem4290604 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290595 A f s x h1 h2) (fun h3 : False => @lem4290251 A s x h1)). Qed.
Lemma lem4290605 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290604 A f s x h1 h2) (@lem4290251 A s x h1)). Qed.
Lemma lem4290606 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : (term77 A s x) = False.
Proof. exact (prop_ext (fun h3 : term77 A s x => @lem4290605 A f s x h1 h2) (fun h3 : False => @lem4290247 A s x h1)). Qed.
Lemma lem4290607 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (EQ_MP (@lem4290606 A f s x h1 h2) (@lem4290247 A s x h1)). Qed.
Lemma lem4290608 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term215 A f s x) (h2 : (f x) = x) : False.
Proof. exact (or_elim (@lem4290209 A f s x h1) (fun h0 : term77 A s x => @lem4290601 A f s x h0 h1) (fun h0 : term176 A f x => @lem4290599 A f x h0 h2)). Qed.
Lemma lem4290609 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term77 A s x) (h2 : term215 A f s x) : False.
Proof. exact (or_elim (@lem4290209 A f s x h2) (fun h0 : term77 A s x => @lem4290607 A f s x h1 h2) (fun h0 : term176 A f x => @lem4290603 A f s x h1 h2)). Qed.
Lemma lem4290610 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term215 A f s x) : False.
Proof. exact (or_elim (@lem4290208 A f s x h1) (fun h0 : term77 A s x => @lem4290609 A f s x h0 h1) (fun h0 : (f x) = x => @lem4290608 A s f x h1 h0)). Qed.
Lemma lem4290611 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term219 A f s x) : False.
Proof. exact (or_elim (@lem4290199 A f s x h1) (fun h0 : term155 A s f x => @lem4290368 A f s x h0 h1) (fun h0 : term177 A s f x => @lem4290413 A f s x h0 h1)). Qed.
Lemma lem4290612 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term199 A f s x) : False.
Proof. exact (or_elim (@lem4290195 A f s x h1) (fun h0 : term219 A f s x => @lem4290611 A f s x h0) (fun h0 : term215 A f s x => @lem4290610 A f s x h0)). Qed.
Lemma lem4290613 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term199 A f s x) : (term199 A f s x) = False.
Proof. exact (prop_ext (fun h2 : term199 A f s x => @lem4290612 A f s x h1) (fun h2 : False => @lem4290059 A f s x h1)). Qed.
Lemma lem4290614 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) (h1 : term199 A f s x) : False.
Proof. exact (EQ_MP (@lem4290613 A f s x h1) (@lem4290059 A f s x h1)). Qed.
Lemma lem4290615 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : term198 A f s x.
Proof. exact (fun h0 : term199 A f s x => @lem4290614 A f s x h0). Qed.
Lemma lem4290616 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : (term178 A s f x) = (s x).
Proof. exact (EQ_MP (@lem4290058 A f s x) (@lem4290615 A f s x)). Qed.
Lemma lem4290621 {A : Type'} (f : A -> A) (s : A -> Prop) : term183 A f s.
Proof. exact (fun x : A => @lem4290616 A f s x). Qed.
Lemma lem4290626 {A : Type'} (s : A -> Prop) : term193 A s.
Proof. exact (fun f : A -> A => @lem4290621 A f s). Qed.
Lemma lem4290631 {A : Type'} : term197 A.
Proof. exact (fun s : A -> Prop => @lem4290626 A s). Qed.
Lemma lem4290632 {A : Type'} : term196 A.
Proof. exact (EQ_MP (@lem4290054 A) (@lem4290631 A)). Qed.
Lemma lem4290633 {A : Type'} (s : A -> Prop) : term222 A s.
Proof. exact (@lem4290632 A s). Qed.
Lemma lem4290634 {A : Type'} (s : A -> Prop) : (term222 A s) = (term192 A s).
Proof. exact (eq_refl (term222 A s)). Qed.
Lemma lem4290635 {A : Type'} (s : A -> Prop) : term192 A s.
Proof. exact (EQ_MP (@lem4290634 A s) (@lem4290633 A s)). Qed.
Lemma lem4290636 {A : Type'} (s : A -> Prop) (f : A -> A) : term223 A s f.
Proof. exact (@lem4290635 A s f). Qed.
Lemma lem4290637 {A : Type'} (f : A -> A) (s : A -> Prop) : (term223 A s f) = (term184 A f s).
Proof. exact (eq_refl (term223 A s f)). Qed.
Lemma lem4290638 {A : Type'} (f : A -> A) (s : A -> Prop) : term184 A f s.
Proof. exact (EQ_MP (@lem4290637 A f s) (@lem4290636 A s f)). Qed.
Lemma lem4290640 {A : Type'} (f : A -> A) (s : A -> Prop) : term184 A f s.
Proof. exact (@lem4289955 A f s (@lem4290638 A f s)). Qed.
Lemma lem4290641 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term185 A f s) : False.
Proof. exact (@lem4290640 A f s (@lem4289939 A f s h1)). Qed.
Lemma lem4290642 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term185 A f s) : (term185 A f s) = False.
Proof. exact (prop_ext (fun h2 : term185 A f s => @lem4290641 A f s h1) (fun h2 : False => @lem4289939 A f s h1)). Qed.
Lemma lem4290643 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term185 A f s) : False.
Proof. exact (EQ_MP (@lem4290642 A f s h1) (@lem4289939 A f s h1)). Qed.
Lemma lem4290644 {A : Type'} (f : A -> A) (s : A -> Prop) : term184 A f s.
Proof. exact (fun h0 : term185 A f s => @lem4290643 A f s h0). Qed.
Lemma lem4290645 {A : Type'} (f : A -> A) (s : A -> Prop) : term183 A f s.
Proof. exact (EQ_MP (@lem4289938 A f s) (@lem4290644 A f s)). Qed.
Lemma lem4290646 {A : Type'} (f : A -> A) (s : A -> Prop) : term130 A f s.
Proof. exact (EQ_MP (@lem4289934 A f s) (@lem4290645 A f s)). Qed.
Lemma lem4290647 {A : Type'} (f : A -> A) (s : A -> Prop) : (term129 A s f) = s.
Proof. exact (EQ_MP (@lem4289825 A f s) (@lem4290646 A f s)). Qed.
Lemma lem4290648 {A : Type'} (f : A -> A) (s : A -> Prop) : (term224 A s f) = (@CARD A s).
Proof. exact (MK_COMB (@lem4289790 A) (@lem4290647 A f s)). Qed.
Lemma lem4290649 {A : Type'} (f : A -> A) (s : A -> Prop) : (term225 A s f) = (term6 A s).
Proof. exact (MK_COMB (@lem4289789) (@lem4290648 A f s)). Qed.
Lemma lem4290650 {A : Type'} (s : A -> Prop) : term226 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem4290651 {A : Type'} (s : A -> Prop) : (term226 A s) = (term227 A s).
Proof. exact (eq_refl (term226 A s)). Qed.
Lemma lem4290652 {A : Type'} (s : A -> Prop) : term227 A s.
Proof. exact (EQ_MP (@lem4290651 A s) (@lem4290650 A s)). Qed.
Lemma lem4290653 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term228 A s P.
Proof. exact (@lem4290652 A s P). Qed.
Lemma lem4290654 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term228 A s P) = (term229 A s P).
Proof. exact (eq_refl (term228 A s P)). Qed.
Lemma lem4290655 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term229 A s P.
Proof. exact (EQ_MP (@lem4290654 A s P) (@lem4290653 A s P)). Qed.
Lemma lem4290656 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4290657 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term230 A s P.
Proof. exact (@lem4290655 A s P (@lem4290656 A s h1)). Qed.
Lemma lem4290658 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term230 A s P) = ((term230 A s P) = True).
Proof. exact (@lem7 (term230 A s P)). Qed.
Lemma lem4290659 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term230 A s P) = True.
Proof. exact (EQ_MP (@lem4290658 A s P) (@lem4290657 A P s h1)). Qed.
Lemma lem4290665 {A : Type'} (s : A -> Prop) : term231 A s.
Proof. exact (@lem3843862 A s). Qed.
Lemma lem4290666 {A : Type'} (s : A -> Prop) : (term231 A s) = (term232 A s).
Proof. exact (eq_refl (term231 A s)). Qed.
Lemma lem4290667 {A : Type'} (s : A -> Prop) : term232 A s.
Proof. exact (EQ_MP (@lem4290666 A s) (@lem4290665 A s)). Qed.
Lemma lem4290668 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term233 A s t.
Proof. exact (@lem4290667 A s t). Qed.
Lemma lem4290669 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term233 A s t) = (term234 A s t).
Proof. exact (eq_refl (term233 A s t)). Qed.
Lemma lem4290670 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term234 A s t.
Proof. exact (EQ_MP (@lem4290669 A s t) (@lem4290668 A s t)). Qed.
Lemma lem4290671 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term235 A s t) : term235 A s t.
Proof. exact (h1). Qed.
Lemma lem4290672 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term235 A s t) : (term236 A s t) = (term237 A s t).
Proof. exact (@lem4290670 A s t (@lem4290671 A s t h1)). Qed.
Lemma lem4290678 (m : nat) : term238 m.
Proof. exact (@lem125496 m). Qed.
Lemma lem4290679 (m : nat) : (term238 m) = (term239 m).
Proof. exact (eq_refl (term238 m)). Qed.
Lemma lem4290680 (m : nat) : term239 m.
Proof. exact (EQ_MP (@lem4290679 m) (@lem4290678 m)). Qed.
Lemma lem4290681 (m : nat) (n : nat) : term240 m n.
Proof. exact (@lem4290680 m n). Qed.
Lemma lem4290682 (m : nat) (n : nat) : (term240 m n) = ((term241 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (eq_refl (term240 m n)). Qed.
Lemma lem4290684 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4290716 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term234 A s t.
Proof. exact (fun h0 : term235 A s t => @lem4290672 A s t h0). Qed.
Lemma lem4290717 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term234 A s t.
Proof. exact (@lem4290716 A s t). Qed.
Lemma lem4290718 {A : Type'} (s : A -> Prop) (f : A -> A) : term242 A s f.
Proof. exact (@lem4290717 A (term135 A s f) (term136 A s f)). Qed.
Lemma lem4290722 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term243 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem4290659 A P s h0). Qed.
Lemma lem4290723 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term243 A s P.
Proof. exact (@lem4290722 A s P). Qed.
Lemma lem4290724 {A : Type'} (s : A -> Prop) (f : A -> A) : term244 A s f.
Proof. exact (@lem4290723 A s (term245 A f)). Qed.
Lemma lem4290725 {A : Type'} (f : A -> A) (x : A) : (term246 A f x) = ((f x) = x).
Proof. exact (eq_refl (term246 A f x)). Qed.
Lemma lem4290726 {A : Type'} (x : A) (s : A -> Prop) : (term54 A x s) = (term54 A x s).
Proof. exact (eq_refl (term54 A x s)). Qed.
Lemma lem4290727 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term247 A s f x) = (term140 A s f x).
Proof. exact (MK_COMB (@lem4290726 A x s) (@lem4290725 A f x)). Qed.
Lemma lem4290728 {A : Type'} (GEN_PVAR_116 : A) : (@SETSPEC A GEN_PVAR_116) = (@SETSPEC A GEN_PVAR_116).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_116)). Qed.
Lemma lem4290729 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term248 A GEN_PVAR_116 s f x) = (term142 A GEN_PVAR_116 s f x).
Proof. exact (MK_COMB (@lem4290728 A GEN_PVAR_116) (@lem4290727 A s f x)). Qed.
Lemma lem4290730 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4290731 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term249 A GEN_PVAR_116 s f x) = (term144 A GEN_PVAR_116 s f x).
Proof. exact (MK_COMB (@lem4290729 A GEN_PVAR_116 s f x) (@lem4290730 A x)). Qed.
Lemma lem4290732 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) : (term250 A GEN_PVAR_116 s f) = (term146 A GEN_PVAR_116 s f).
Proof. exact (fun_ext (fun x : A => @lem4290731 A GEN_PVAR_116 s f x)). Qed.
Lemma lem4290733 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4290734 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) : (term251 A GEN_PVAR_116 s f) = (term148 A GEN_PVAR_116 s f).
Proof. exact (MK_COMB (@lem4290733 A) (@lem4290732 A GEN_PVAR_116 s f)). Qed.
Lemma lem4290735 {A : Type'} (s : A -> Prop) (f : A -> A) : (term252 A s f) = (term150 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_116 : A => @lem4290734 A GEN_PVAR_116 s f)). Qed.
Lemma lem4290736 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4290737 {A : Type'} (s : A -> Prop) (f : A -> A) : (term253 A s f) = (term135 A s f).
Proof. exact (MK_COMB (@lem4290736 A) (@lem4290735 A s f)). Qed.
Lemma lem4290738 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem4290739 {A : Type'} (s : A -> Prop) (f : A -> A) : (term254 A s f) = (term255 A s f).
Proof. exact (MK_COMB (@lem4290738 A) (@lem4290737 A s f)). Qed.
Lemma lem4290740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4290741 {A : Type'} (s : A -> Prop) (f : A -> A) : (term256 A s f) = (term257 A s f).
Proof. exact (MK_COMB (@lem4290740) (@lem4290739 A s f)). Qed.
Lemma lem4290742 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem4290743 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term254 A s f) = True) = ((term255 A s f) = True).
Proof. exact (MK_COMB (@lem4290741 A s f) (@lem4290742)). Qed.
Lemma lem4290744 {A : Type'} (s : A -> Prop) : (term258 A s) = (term258 A s).
Proof. exact (eq_refl (term258 A s)). Qed.
Lemma lem4290745 {A : Type'} (s : A -> Prop) (f : A -> A) : (term244 A s f) = (term259 A s f).
Proof. exact (MK_COMB (@lem4290744 A s) (@lem4290743 A s f)). Qed.
Lemma lem4290746 {A : Type'} (s : A -> Prop) (f : A -> A) : term259 A s f.
Proof. exact (EQ_MP (@lem4290745 A s f) (@lem4290724 A s f)). Qed.
Lemma lem4290748 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4290684 A s) (@lem4289756 A s h1)). Qed.
Lemma lem4290749 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4290748 A s h1)). Qed.
Lemma lem4290750 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4290749 A s h1) (@lem0)). Qed.
Lemma lem4290751 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term255 A s f) = True.
Proof. exact (@lem4290746 A s f (@lem4290750 A s h1)). Qed.
Lemma lem4290752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4290753 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term260 A s f) = (and True).
Proof. exact (MK_COMB (@lem4290752) (@lem4290751 A f s h1)). Qed.
Lemma lem4290757 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term243 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem4290659 A P s h0). Qed.
Lemma lem4290758 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term243 A s P.
Proof. exact (@lem4290757 A s P). Qed.
Lemma lem4290759 {A : Type'} (s : A -> Prop) (f : A -> A) : term261 A s f.
Proof. exact (@lem4290758 A s (term262 A f)). Qed.
Lemma lem4290760 {A : Type'} (f : A -> A) (x : A) : (term263 A f x) = (term176 A f x).
Proof. exact (eq_refl (term263 A f x)). Qed.
Lemma lem4290761 {A : Type'} (x : A) (s : A -> Prop) : (term54 A x s) = (term54 A x s).
Proof. exact (eq_refl (term54 A x s)). Qed.
Lemma lem4290762 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term264 A s f x) = (term161 A s f x).
Proof. exact (MK_COMB (@lem4290761 A x s) (@lem4290760 A f x)). Qed.
Lemma lem4290763 {A : Type'} (GEN_PVAR_117 : A) : (@SETSPEC A GEN_PVAR_117) = (@SETSPEC A GEN_PVAR_117).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_117)). Qed.
Lemma lem4290764 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term265 A GEN_PVAR_117 s f x) = (term163 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4290763 A GEN_PVAR_117) (@lem4290762 A s f x)). Qed.
Lemma lem4290765 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4290766 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term266 A GEN_PVAR_117 s f x) = (term165 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4290764 A GEN_PVAR_117 s f x) (@lem4290765 A x)). Qed.
Lemma lem4290767 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term267 A GEN_PVAR_117 s f) = (term167 A GEN_PVAR_117 s f).
Proof. exact (fun_ext (fun x : A => @lem4290766 A GEN_PVAR_117 s f x)). Qed.
Lemma lem4290768 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4290769 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term268 A GEN_PVAR_117 s f) = (term169 A GEN_PVAR_117 s f).
Proof. exact (MK_COMB (@lem4290768 A) (@lem4290767 A GEN_PVAR_117 s f)). Qed.
Lemma lem4290770 {A : Type'} (s : A -> Prop) (f : A -> A) : (term269 A s f) = (term171 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_117 : A => @lem4290769 A GEN_PVAR_117 s f)). Qed.
Lemma lem4290771 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4290772 {A : Type'} (s : A -> Prop) (f : A -> A) : (term270 A s f) = (term136 A s f).
Proof. exact (MK_COMB (@lem4290771 A) (@lem4290770 A s f)). Qed.
Lemma lem4290773 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem4290774 {A : Type'} (s : A -> Prop) (f : A -> A) : (term271 A s f) = (term272 A s f).
Proof. exact (MK_COMB (@lem4290773 A) (@lem4290772 A s f)). Qed.
Lemma lem4290775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4290776 {A : Type'} (s : A -> Prop) (f : A -> A) : (term273 A s f) = (term274 A s f).
Proof. exact (MK_COMB (@lem4290775) (@lem4290774 A s f)). Qed.
Lemma lem4290777 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem4290778 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term271 A s f) = True) = ((term272 A s f) = True).
Proof. exact (MK_COMB (@lem4290776 A s f) (@lem4290777)). Qed.
Lemma lem4290779 {A : Type'} (s : A -> Prop) : (term258 A s) = (term258 A s).
Proof. exact (eq_refl (term258 A s)). Qed.
Lemma lem4290780 {A : Type'} (s : A -> Prop) (f : A -> A) : (term261 A s f) = (term275 A s f).
Proof. exact (MK_COMB (@lem4290779 A s) (@lem4290778 A s f)). Qed.
Lemma lem4290781 {A : Type'} (s : A -> Prop) (f : A -> A) : term275 A s f.
Proof. exact (EQ_MP (@lem4290780 A s f) (@lem4290759 A s f)). Qed.
Lemma lem4290783 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4290684 A s) (@lem4289756 A s h1)). Qed.
Lemma lem4290784 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4290783 A s h1)). Qed.
Lemma lem4290785 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4290784 A s h1) (@lem0)). Qed.
Lemma lem4290786 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term272 A s f) = True.
Proof. exact (@lem4290781 A s f (@lem4290785 A s h1)). Qed.
Lemma lem4290787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4290788 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term276 A s f) = (and True).
Proof. exact (MK_COMB (@lem4290787) (@lem4290786 A f s h1)). Qed.
Lemma lem4290792 {_102950 : Type'} (s : _102950 -> Prop) (P : _102950 -> Prop) : (term27 _102950 s P) = (@EMPTY _102950).
Proof. exact (EQ_MP (@lem4289379 _102950 s P) (@lem4289742 _102950 s P)). Qed.
Lemma lem4290793 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term27 A s P) = (@EMPTY A).
Proof. exact (@lem4290792 A s P). Qed.
Lemma lem4290794 {A : Type'} (s : A -> Prop) (f : A -> A) : (term277 A s f) = (@EMPTY A).
Proof. exact (@lem4290793 A s (term245 A f)). Qed.
Lemma lem4290795 {A : Type'} (f : A -> A) (x : A) : (term246 A f x) = ((f x) = x).
Proof. exact (eq_refl (term246 A f x)). Qed.
Lemma lem4290796 {A : Type'} (x : A) (s : A -> Prop) : (term54 A x s) = (term54 A x s).
Proof. exact (eq_refl (term54 A x s)). Qed.
Lemma lem4290797 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term247 A s f x) = (term140 A s f x).
Proof. exact (MK_COMB (@lem4290796 A x s) (@lem4290795 A f x)). Qed.
Lemma lem4290798 {A : Type'} (GEN_PVAR_116 : A) : (@SETSPEC A GEN_PVAR_116) = (@SETSPEC A GEN_PVAR_116).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_116)). Qed.
Lemma lem4290799 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term248 A GEN_PVAR_116 s f x) = (term142 A GEN_PVAR_116 s f x).
Proof. exact (MK_COMB (@lem4290798 A GEN_PVAR_116) (@lem4290797 A s f x)). Qed.
Lemma lem4290800 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4290801 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term249 A GEN_PVAR_116 s f x) = (term144 A GEN_PVAR_116 s f x).
Proof. exact (MK_COMB (@lem4290799 A GEN_PVAR_116 s f x) (@lem4290800 A x)). Qed.
Lemma lem4290802 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) : (term250 A GEN_PVAR_116 s f) = (term146 A GEN_PVAR_116 s f).
Proof. exact (fun_ext (fun x : A => @lem4290801 A GEN_PVAR_116 s f x)). Qed.
Lemma lem4290803 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4290804 {A : Type'} (GEN_PVAR_116 : A) (s : A -> Prop) (f : A -> A) : (term251 A GEN_PVAR_116 s f) = (term148 A GEN_PVAR_116 s f).
Proof. exact (MK_COMB (@lem4290803 A) (@lem4290802 A GEN_PVAR_116 s f)). Qed.
Lemma lem4290805 {A : Type'} (s : A -> Prop) (f : A -> A) : (term252 A s f) = (term150 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_116 : A => @lem4290804 A GEN_PVAR_116 s f)). Qed.
Lemma lem4290806 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4290807 {A : Type'} (s : A -> Prop) (f : A -> A) : (term253 A s f) = (term135 A s f).
Proof. exact (MK_COMB (@lem4290806 A) (@lem4290805 A s f)). Qed.
Lemma lem4290808 {A : Type'} : (@INTER A) = (@INTER A).
Proof. exact (eq_refl (@INTER A)). Qed.
Lemma lem4290809 {A : Type'} (s : A -> Prop) (f : A -> A) : (term278 A s f) = (term279 A s f).
Proof. exact (MK_COMB (@lem4290808 A) (@lem4290807 A s f)). Qed.
Lemma lem4290810 {A : Type'} (f : A -> A) (x : A) : (term246 A f x) = ((f x) = x).
Proof. exact (eq_refl (term246 A f x)). Qed.
Lemma lem4290811 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4290812 {A : Type'} (f : A -> A) (x : A) : (term280 A f x) = (term176 A f x).
Proof. exact (MK_COMB (@lem4290811) (@lem4290810 A f x)). Qed.
Lemma lem4290813 {A : Type'} (x : A) (s : A -> Prop) : (term54 A x s) = (term54 A x s).
Proof. exact (eq_refl (term54 A x s)). Qed.
Lemma lem4290814 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term281 A s f x) = (term161 A s f x).
Proof. exact (MK_COMB (@lem4290813 A x s) (@lem4290812 A f x)). Qed.
Lemma lem4290815 {A : Type'} (GEN_PVAR_117 : A) : (@SETSPEC A GEN_PVAR_117) = (@SETSPEC A GEN_PVAR_117).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_117)). Qed.
Lemma lem4290816 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term282 A GEN_PVAR_117 s f x) = (term163 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4290815 A GEN_PVAR_117) (@lem4290814 A s f x)). Qed.
Lemma lem4290817 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4290818 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term283 A GEN_PVAR_117 s f x) = (term165 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4290816 A GEN_PVAR_117 s f x) (@lem4290817 A x)). Qed.
Lemma lem4290819 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term284 A GEN_PVAR_117 s f) = (term167 A GEN_PVAR_117 s f).
Proof. exact (fun_ext (fun x : A => @lem4290818 A GEN_PVAR_117 s f x)). Qed.
Lemma lem4290820 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4290821 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term285 A GEN_PVAR_117 s f) = (term169 A GEN_PVAR_117 s f).
Proof. exact (MK_COMB (@lem4290820 A) (@lem4290819 A GEN_PVAR_117 s f)). Qed.
Lemma lem4290822 {A : Type'} (s : A -> Prop) (f : A -> A) : (term286 A s f) = (term171 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_117 : A => @lem4290821 A GEN_PVAR_117 s f)). Qed.
Lemma lem4290823 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4290824 {A : Type'} (s : A -> Prop) (f : A -> A) : (term287 A s f) = (term136 A s f).
Proof. exact (MK_COMB (@lem4290823 A) (@lem4290822 A s f)). Qed.
Lemma lem4290825 {A : Type'} (s : A -> Prop) (f : A -> A) : (term277 A s f) = (term288 A s f).
Proof. exact (MK_COMB (@lem4290809 A s f) (@lem4290824 A s f)). Qed.
Lemma lem4290826 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4290827 {A : Type'} (s : A -> Prop) (f : A -> A) : (term289 A s f) = (term290 A s f).
Proof. exact (MK_COMB (@lem4290826 A) (@lem4290825 A s f)). Qed.
Lemma lem4290828 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4290829 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term277 A s f) = (@EMPTY A)) = ((term288 A s f) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4290827 A s f) (@lem4290828 A)). Qed.
Lemma lem4290830 {A : Type'} (s : A -> Prop) (f : A -> A) : (term288 A s f) = (@EMPTY A).
Proof. exact (EQ_MP (@lem4290829 A s f) (@lem4290794 A s f)). Qed.
Lemma lem4290831 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4290832 {A : Type'} (s : A -> Prop) (f : A -> A) : (term290 A s f) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem4290831 A) (@lem4290830 A s f)). Qed.
Lemma lem4290833 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4290834 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term288 A s f) = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4290832 A s f) (@lem4290833 A)). Qed.
Lemma lem4290836 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4290837 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4290836 (A -> Prop) x). Qed.
Lemma lem4290838 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem4290837 A (@EMPTY A)). Qed.
Lemma lem4290839 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term288 A s f) = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem4290834 A s f) (@lem4290838 A)). Qed.
Lemma lem4290840 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term291 A s f) = (True /\ True).
Proof. exact (MK_COMB (@lem4290788 A f s h1) (@lem4290839 A s f)). Qed.
Lemma lem4290842 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4290843 : (True /\ True) = True.
Proof. exact (@lem4290842 True). Qed.
Lemma lem4290844 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term291 A s f) = True.
Proof. exact (TRANS (@lem4290840 A f s h1) (@lem4290843)). Qed.
Lemma lem4290845 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term292 A s f) = (True /\ True).
Proof. exact (MK_COMB (@lem4290753 A f s h1) (@lem4290844 A f s h1)). Qed.
Lemma lem4290847 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4290848 : (True /\ True) = True.
Proof. exact (@lem4290847 True). Qed.
Lemma lem4290849 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term292 A s f) = True.
Proof. exact (TRANS (@lem4290845 A f s h1) (@lem4290848)). Qed.
Lemma lem4290850 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : True = (term292 A s f).
Proof. exact (SYM (@lem4290849 A f s h1)). Qed.
Lemma lem4290851 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : term292 A s f.
Proof. exact (EQ_MP (@lem4290850 A f s h1) (@lem0)). Qed.
Lemma lem4290852 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term224 A s f) = (term293 A s f).
Proof. exact (@lem4290718 A s f (@lem4290851 A f s h1)). Qed.
Lemma lem4290869 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem4290870 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term225 A s f) = (term294 A s f).
Proof. exact (MK_COMB (@lem4290869) (@lem4290852 A f s h1)). Qed.
Lemma lem4290872 (m : nat) (n : nat) : (term241 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem4290682 m n) (@lem4290681 m n)). Qed.
Lemma lem4290873 {A : Type'} (s : A -> Prop) (f : A -> A) : (term294 A s f) = ((term128 A s f) = (term295 A s f)).
Proof. exact (@lem4290872 (term296 A s f) (term297 A s f)). Qed.
Lemma lem4290892 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term225 A s f) = ((term128 A s f) = (term295 A s f)).
Proof. exact (TRANS (@lem4290870 A f s h1) (@lem4290873 A s f)). Qed.
Lemma lem4290893 {A : Type'} (s : A -> Prop) (f : A -> A) : (term298 A s f) = (term298 A s f).
Proof. exact (eq_refl (term298 A s f)). Qed.
Lemma lem4290894 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : ((term128 A s f) = (term225 A s f)) = ((term128 A s f) = ((term128 A s f) = (term295 A s f))).
Proof. exact (MK_COMB (@lem4290893 A s f) (@lem4290892 A f s h1)). Qed.
Lemma lem4290923 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : ((term128 A s f) = ((term128 A s f) = (term295 A s f))) = ((term128 A s f) = (term225 A s f)).
Proof. exact (SYM (@lem4290894 A f s h1)). Qed.
Lemma lem4290925 (p : Prop) (q : Prop) : (p = (p = q)) = q.
Proof. exact (or_elim (@lem4289255 p) (fun h0 : p = True => @lem4289339 q p h0) (fun h0 : p = False => @lem4289338 q p h0)). Qed.
Lemma lem4290926 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f).
Proof. exact (@lem4290925 (term128 A s f) (term295 A s f)). Qed.
Lemma lem4290929 {A : Type'} (s : A -> Prop) (f : A -> A) : (term299 A s f) = (term299 A s f).
Proof. exact (eq_refl (term299 A s f)). Qed.
Lemma lem4290930 {A : Type'} (s : A -> Prop) (f : A -> A) : (term299 A s f) = (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f)).
Proof. exact (eq_refl (term299 A s f)). Qed.
Lemma lem4290931 {A : Type'} (s : A -> Prop) (f : A -> A) : (term300 A s f) = (term300 A s f).
Proof. exact (eq_refl (term300 A s f)). Qed.
Lemma lem4290932 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term299 A s f) = (term299 A s f)) = ((term299 A s f) = (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f))).
Proof. exact (MK_COMB (@lem4290931 A s f) (@lem4290930 A s f)). Qed.
Lemma lem4290933 {A : Type'} (s : A -> Prop) (f : A -> A) : (term299 A s f) = (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f)).
Proof. exact (eq_refl (term299 A s f)). Qed.
Lemma lem4290934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4290935 {A : Type'} (s : A -> Prop) (f : A -> A) : (term300 A s f) = (term301 A s f).
Proof. exact (MK_COMB (@lem4290934) (@lem4290933 A s f)). Qed.
Lemma lem4290936 {A : Type'} (s : A -> Prop) (f : A -> A) : (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f)) = (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f)).
Proof. exact (eq_refl (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f))). Qed.
Lemma lem4290937 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term299 A s f) = (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f))) = ((((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f)) = (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f))).
Proof. exact (MK_COMB (@lem4290935 A s f) (@lem4290936 A s f)). Qed.
Lemma lem4290938 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term299 A s f) = (term299 A s f)) = ((((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f)) = (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f))).
Proof. exact (TRANS (@lem4290932 A s f) (@lem4290937 A s f)). Qed.
Lemma lem4290939 {A : Type'} (s : A -> Prop) (f : A -> A) : (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f)) = (((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f)).
Proof. exact (EQ_MP (@lem4290938 A s f) (@lem4290929 A s f)). Qed.
Lemma lem4290940 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term128 A s f) = ((term128 A s f) = (term295 A s f))) = (term295 A s f).
Proof. exact (EQ_MP (@lem4290939 A s f) (@lem4290926 A s f)). Qed.
Lemma lem4290949 {A : Type'} (s : A -> Prop) (f : A -> A) : (term295 A s f) = ((term128 A s f) = ((term128 A s f) = (term295 A s f))).
Proof. exact (SYM (@lem4290940 A s f)). Qed.
Lemma lem4290951 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem4289243 A s) (@lem4289242 A s)). Qed.
Lemma lem4290952 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem4290951 A s). Qed.
Lemma lem4290953 {A : Type'} (s : A -> Prop) (f : A -> A) : term302 A s f.
Proof. exact (@lem4290952 A (term136 A s f)). Qed.
Lemma lem4290954 {A : Type'} (s : A -> Prop) : term226 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem4290955 {A : Type'} (s : A -> Prop) : (term226 A s) = (term227 A s).
Proof. exact (eq_refl (term226 A s)). Qed.
Lemma lem4290956 {A : Type'} (s : A -> Prop) : term227 A s.
Proof. exact (EQ_MP (@lem4290955 A s) (@lem4290954 A s)). Qed.
Lemma lem4290957 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term228 A s P.
Proof. exact (@lem4290956 A s P). Qed.
Lemma lem4290958 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term228 A s P) = (term229 A s P).
Proof. exact (eq_refl (term228 A s P)). Qed.
Lemma lem4290959 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term229 A s P.
Proof. exact (EQ_MP (@lem4290958 A s P) (@lem4290957 A s P)). Qed.
Lemma lem4290960 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4290961 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term230 A s P.
Proof. exact (@lem4290959 A s P (@lem4290960 A s h1)). Qed.
Lemma lem4290962 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term230 A s P) = ((term230 A s P) = True).
Proof. exact (@lem7 (term230 A s P)). Qed.
Lemma lem4290963 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term230 A s P) = True.
Proof. exact (EQ_MP (@lem4290962 A s P) (@lem4290961 A P s h1)). Qed.
Lemma lem4290969 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4290993 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term243 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem4290963 A P s h0). Qed.
Lemma lem4290994 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term243 A s P.
Proof. exact (@lem4290993 A s P). Qed.
Lemma lem4290995 {A : Type'} (s : A -> Prop) (f : A -> A) : term261 A s f.
Proof. exact (@lem4290994 A s (term262 A f)). Qed.
Lemma lem4290996 {A : Type'} (f : A -> A) (x : A) : (term263 A f x) = (term176 A f x).
Proof. exact (eq_refl (term263 A f x)). Qed.
Lemma lem4290997 {A : Type'} (x : A) (s : A -> Prop) : (term54 A x s) = (term54 A x s).
Proof. exact (eq_refl (term54 A x s)). Qed.
Lemma lem4290998 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term264 A s f x) = (term161 A s f x).
Proof. exact (MK_COMB (@lem4290997 A x s) (@lem4290996 A f x)). Qed.
Lemma lem4290999 {A : Type'} (GEN_PVAR_117 : A) : (@SETSPEC A GEN_PVAR_117) = (@SETSPEC A GEN_PVAR_117).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_117)). Qed.
Lemma lem4291000 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term265 A GEN_PVAR_117 s f x) = (term163 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4290999 A GEN_PVAR_117) (@lem4290998 A s f x)). Qed.
Lemma lem4291001 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4291002 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term266 A GEN_PVAR_117 s f x) = (term165 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4291000 A GEN_PVAR_117 s f x) (@lem4291001 A x)). Qed.
Lemma lem4291003 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term267 A GEN_PVAR_117 s f) = (term167 A GEN_PVAR_117 s f).
Proof. exact (fun_ext (fun x : A => @lem4291002 A GEN_PVAR_117 s f x)). Qed.
Lemma lem4291004 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4291005 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term268 A GEN_PVAR_117 s f) = (term169 A GEN_PVAR_117 s f).
Proof. exact (MK_COMB (@lem4291004 A) (@lem4291003 A GEN_PVAR_117 s f)). Qed.
Lemma lem4291006 {A : Type'} (s : A -> Prop) (f : A -> A) : (term269 A s f) = (term171 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_117 : A => @lem4291005 A GEN_PVAR_117 s f)). Qed.
Lemma lem4291007 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4291008 {A : Type'} (s : A -> Prop) (f : A -> A) : (term270 A s f) = (term136 A s f).
Proof. exact (MK_COMB (@lem4291007 A) (@lem4291006 A s f)). Qed.
Lemma lem4291009 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem4291010 {A : Type'} (s : A -> Prop) (f : A -> A) : (term271 A s f) = (term272 A s f).
Proof. exact (MK_COMB (@lem4291009 A) (@lem4291008 A s f)). Qed.
Lemma lem4291011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4291012 {A : Type'} (s : A -> Prop) (f : A -> A) : (term273 A s f) = (term274 A s f).
Proof. exact (MK_COMB (@lem4291011) (@lem4291010 A s f)). Qed.
Lemma lem4291013 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem4291014 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term271 A s f) = True) = ((term272 A s f) = True).
Proof. exact (MK_COMB (@lem4291012 A s f) (@lem4291013)). Qed.
Lemma lem4291015 {A : Type'} (s : A -> Prop) : (term258 A s) = (term258 A s).
Proof. exact (eq_refl (term258 A s)). Qed.
Lemma lem4291016 {A : Type'} (s : A -> Prop) (f : A -> A) : (term261 A s f) = (term275 A s f).
Proof. exact (MK_COMB (@lem4291015 A s) (@lem4291014 A s f)). Qed.
Lemma lem4291017 {A : Type'} (s : A -> Prop) (f : A -> A) : term275 A s f.
Proof. exact (EQ_MP (@lem4291016 A s f) (@lem4290995 A s f)). Qed.
Lemma lem4291019 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4290969 A s) (@lem4289756 A s h1)). Qed.
Lemma lem4291020 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4291019 A s h1)). Qed.
Lemma lem4291021 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4291020 A s h1) (@lem0)). Qed.
Lemma lem4291022 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term272 A s f) = True.
Proof. exact (@lem4291017 A s f (@lem4291021 A s h1)). Qed.
Lemma lem4291023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291024 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term276 A s f) = (and True).
Proof. exact (MK_COMB (@lem4291023) (@lem4291022 A f s h1)). Qed.
Lemma lem4291110 {A : Type'} (s : A -> Prop) (f : A -> A) : (term303 A s f) = (term303 A s f).
Proof. exact (eq_refl (term303 A s f)). Qed.
Lemma lem4291111 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term304 A s f) = (term305 A s f).
Proof. exact (MK_COMB (@lem4291024 A f s h1) (@lem4291110 A s f)). Qed.
Lemma lem4291113 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4291114 {A : Type'} (s : A -> Prop) (f : A -> A) : (term305 A s f) = (term303 A s f).
Proof. exact (@lem4291113 (term303 A s f)). Qed.
Lemma lem4291200 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term304 A s f) = (term303 A s f).
Proof. exact (TRANS (@lem4291111 A f s h1) (@lem4291114 A s f)). Qed.
Lemma lem4291201 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term303 A s f) = (term304 A s f).
Proof. exact (SYM (@lem4291200 A f s h1)). Qed.
Lemma lem4291212 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : term306 A f s.
Proof. exact (conj (@lem4289755 A s f h1) (@lem4289756 A s h2)). Qed.
Lemma lem4291280 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4291281 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4291280 A P x). Qed.
Lemma lem4291282 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4291281 A s x). Qed.
Lemma lem4291283 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4291284 {A : Type'} (s : A -> Prop) (x : A) : (term307 A x s) = (term308 A s x).
Proof. exact (MK_COMB (@lem4291283) (@lem4291282 A s x)). Qed.
Lemma lem4291288 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4291289 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4291288 A P x). Qed.
Lemma lem4291290 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term309 A f x s) = (term310 A s f x).
Proof. exact (@lem4291289 A s (f x)). Qed.
Lemma lem4291291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291292 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term311 A f x s) = (term312 A s f x).
Proof. exact (MK_COMB (@lem4291291) (@lem4291290 A s f x)). Qed.
Lemma lem4291295 {A : Type'} (f : A -> A) (x : A) : ((term313 A f x) = x) = ((term313 A f x) = x).
Proof. exact (eq_refl ((term313 A f x) = x)). Qed.
Lemma lem4291296 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term314 A s f x) = (term315 A s f x).
Proof. exact (MK_COMB (@lem4291292 A s f x) (@lem4291295 A f x)). Qed.
Lemma lem4291299 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term316 A s f x) = (term317 A s f x).
Proof. exact (MK_COMB (@lem4291284 A s x) (@lem4291296 A s f x)). Qed.
Lemma lem4291302 {A : Type'} (s : A -> Prop) (f : A -> A) : (term318 A s f) = (term319 A s f).
Proof. exact (fun_ext (fun x : A => @lem4291299 A s f x)). Qed.
Lemma lem4291303 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4291304 {A : Type'} (s : A -> Prop) (f : A -> A) : (term109 A s f) = (term320 A s f).
Proof. exact (MK_COMB (@lem4291303 A) (@lem4291302 A s f)). Qed.
Lemma lem4291309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291310 {A : Type'} (s : A -> Prop) (f : A -> A) : (term321 A s f) = (term322 A s f).
Proof. exact (MK_COMB (@lem4291309) (@lem4291304 A s f)). Qed.
Lemma lem4291311 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem4291312 {A : Type'} (f : A -> A) (s : A -> Prop) : (term306 A f s) = (term323 A f s).
Proof. exact (MK_COMB (@lem4291310 A s f) (@lem4291311 A s)). Qed.
Lemma lem4291315 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4291316 {A : Type'} (f : A -> A) (s : A -> Prop) : (term324 A f s) = (term325 A f s).
Proof. exact (MK_COMB (@lem4291315) (@lem4291312 A f s)). Qed.
Lemma lem4291324 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4291325 {A : Type'} (p : A -> Prop) (x : A) : (term35 A x p) = (p x).
Proof. exact (@lem4291324 A p x). Qed.
Lemma lem4291326 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term158 A x s f) = (term159 A s f x).
Proof. exact (@lem4291325 A (term160 A s f) x). Qed.
Lemma lem4291327 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term159 A s f x) = (term161 A s f x).
Proof. exact (eq_refl (term159 A s f x)). Qed.
Lemma lem4291328 {A : Type'} (GEN_PVAR_117 : A) : (@SETSPEC A GEN_PVAR_117) = (@SETSPEC A GEN_PVAR_117).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_117)). Qed.
Lemma lem4291329 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term162 A GEN_PVAR_117 s f x) = (term163 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4291328 A GEN_PVAR_117) (@lem4291327 A s f x)). Qed.
Lemma lem4291330 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4291331 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term164 A GEN_PVAR_117 s f x) = (term165 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4291329 A GEN_PVAR_117 s f x) (@lem4291330 A x)). Qed.
Lemma lem4291332 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term166 A GEN_PVAR_117 s f) = (term167 A GEN_PVAR_117 s f).
Proof. exact (fun_ext (fun x : A => @lem4291331 A GEN_PVAR_117 s f x)). Qed.
Lemma lem4291333 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4291334 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term168 A GEN_PVAR_117 s f) = (term169 A GEN_PVAR_117 s f).
Proof. exact (MK_COMB (@lem4291333 A) (@lem4291332 A GEN_PVAR_117 s f)). Qed.
Lemma lem4291335 {A : Type'} (s : A -> Prop) (f : A -> A) : (term170 A s f) = (term171 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_117 : A => @lem4291334 A GEN_PVAR_117 s f)). Qed.
Lemma lem4291336 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4291337 {A : Type'} (s : A -> Prop) (f : A -> A) : (term172 A s f) = (term136 A s f).
Proof. exact (MK_COMB (@lem4291336 A) (@lem4291335 A s f)). Qed.
Lemma lem4291338 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4291339 {A : Type'} (x : A) (s : A -> Prop) (f : A -> A) : (term158 A x s f) = (term173 A x s f).
Proof. exact (MK_COMB (@lem4291338 A x) (@lem4291337 A s f)). Qed.
Lemma lem4291340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4291341 {A : Type'} (x : A) (s : A -> Prop) (f : A -> A) : (term174 A x s f) = (term175 A x s f).
Proof. exact (MK_COMB (@lem4291340) (@lem4291339 A x s f)). Qed.
Lemma lem4291342 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term159 A s f x) = (term161 A s f x).
Proof. exact (eq_refl (term159 A s f x)). Qed.
Lemma lem4291343 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : ((term158 A x s f) = (term159 A s f x)) = ((term173 A x s f) = (term161 A s f x)).
Proof. exact (MK_COMB (@lem4291341 A x s f) (@lem4291342 A s f x)). Qed.
Lemma lem4291344 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term173 A x s f) = (term161 A s f x).
Proof. exact (EQ_MP (@lem4291343 A s f x) (@lem4291326 A s f x)). Qed.
Lemma lem4291348 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4291349 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4291348 A P x). Qed.
Lemma lem4291350 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4291349 A s x). Qed.
Lemma lem4291351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291352 {A : Type'} (s : A -> Prop) (x : A) : (term54 A x s) = (term55 A s x).
Proof. exact (MK_COMB (@lem4291351) (@lem4291350 A s x)). Qed.
Lemma lem4291355 {A : Type'} (f : A -> A) (x : A) : (term176 A f x) = (term176 A f x).
Proof. exact (eq_refl (term176 A f x)). Qed.
Lemma lem4291356 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term161 A s f x) = (term177 A s f x).
Proof. exact (MK_COMB (@lem4291352 A s x) (@lem4291355 A f x)). Qed.
Lemma lem4291359 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term173 A x s f) = (term177 A s f x).
Proof. exact (TRANS (@lem4291344 A s f x) (@lem4291356 A s f x)). Qed.
Lemma lem4291360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4291361 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term326 A x s f) = (term327 A s f x).
Proof. exact (MK_COMB (@lem4291360) (@lem4291359 A s f x)). Qed.
Lemma lem4291365 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4291366 {A : Type'} (p : A -> Prop) (x : A) : (term35 A x p) = (p x).
Proof. exact (@lem4291365 A p x). Qed.
Lemma lem4291367 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term328 A x s f) = (term329 A s f x).
Proof. exact (@lem4291366 A (term160 A s f) (f x)). Qed.
Lemma lem4291368 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term159 A s f x) = (term161 A s f x).
Proof. exact (eq_refl (term159 A s f x)). Qed.
Lemma lem4291369 {A : Type'} (GEN_PVAR_117 : A) : (@SETSPEC A GEN_PVAR_117) = (@SETSPEC A GEN_PVAR_117).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_117)). Qed.
Lemma lem4291370 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term162 A GEN_PVAR_117 s f x) = (term163 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4291369 A GEN_PVAR_117) (@lem4291368 A s f x)). Qed.
Lemma lem4291371 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4291372 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) (x : A) : (term164 A GEN_PVAR_117 s f x) = (term165 A GEN_PVAR_117 s f x).
Proof. exact (MK_COMB (@lem4291370 A GEN_PVAR_117 s f x) (@lem4291371 A x)). Qed.
Lemma lem4291373 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term166 A GEN_PVAR_117 s f) = (term167 A GEN_PVAR_117 s f).
Proof. exact (fun_ext (fun x : A => @lem4291372 A GEN_PVAR_117 s f x)). Qed.
Lemma lem4291374 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4291375 {A : Type'} (GEN_PVAR_117 : A) (s : A -> Prop) (f : A -> A) : (term168 A GEN_PVAR_117 s f) = (term169 A GEN_PVAR_117 s f).
Proof. exact (MK_COMB (@lem4291374 A) (@lem4291373 A GEN_PVAR_117 s f)). Qed.
Lemma lem4291376 {A : Type'} (s : A -> Prop) (f : A -> A) : (term170 A s f) = (term171 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_117 : A => @lem4291375 A GEN_PVAR_117 s f)). Qed.
Lemma lem4291377 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4291378 {A : Type'} (s : A -> Prop) (f : A -> A) : (term172 A s f) = (term136 A s f).
Proof. exact (MK_COMB (@lem4291377 A) (@lem4291376 A s f)). Qed.
Lemma lem4291379 {A : Type'} (f : A -> A) (x : A) : (term330 A f x) = (term330 A f x).
Proof. exact (eq_refl (term330 A f x)). Qed.
Lemma lem4291380 {A : Type'} (x : A) (s : A -> Prop) (f : A -> A) : (term328 A x s f) = (term331 A x s f).
Proof. exact (MK_COMB (@lem4291379 A f x) (@lem4291378 A s f)). Qed.
Lemma lem4291381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4291382 {A : Type'} (x : A) (s : A -> Prop) (f : A -> A) : (term332 A x s f) = (term333 A x s f).
Proof. exact (MK_COMB (@lem4291381) (@lem4291380 A x s f)). Qed.
Lemma lem4291383 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term329 A s f x) = (term334 A s f x).
Proof. exact (eq_refl (term329 A s f x)). Qed.
Lemma lem4291384 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : ((term328 A x s f) = (term329 A s f x)) = ((term331 A x s f) = (term334 A s f x)).
Proof. exact (MK_COMB (@lem4291382 A x s f) (@lem4291383 A s f x)). Qed.
Lemma lem4291385 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term331 A x s f) = (term334 A s f x).
Proof. exact (EQ_MP (@lem4291384 A s f x) (@lem4291367 A s f x)). Qed.
Lemma lem4291389 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4291390 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4291389 A P x). Qed.
Lemma lem4291391 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term309 A f x s) = (term310 A s f x).
Proof. exact (@lem4291390 A s (f x)). Qed.
Lemma lem4291392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291393 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term311 A f x s) = (term312 A s f x).
Proof. exact (MK_COMB (@lem4291392) (@lem4291391 A s f x)). Qed.
Lemma lem4291396 {A : Type'} (f : A -> A) (x : A) : (term335 A f x) = (term335 A f x).
Proof. exact (eq_refl (term335 A f x)). Qed.
Lemma lem4291397 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term334 A s f x) = (term336 A s f x).
Proof. exact (MK_COMB (@lem4291393 A s f x) (@lem4291396 A f x)). Qed.
Lemma lem4291400 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term331 A x s f) = (term336 A s f x).
Proof. exact (TRANS (@lem4291385 A s f x) (@lem4291397 A s f x)). Qed.
Lemma lem4291401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291402 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term337 A x s f) = (term338 A s f x).
Proof. exact (MK_COMB (@lem4291401) (@lem4291400 A s f x)). Qed.
Lemma lem4291409 {A : Type'} (f : A -> A) (x : A) : (term339 A f x) = (term339 A f x).
Proof. exact (eq_refl (term339 A f x)). Qed.
Lemma lem4291410 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term340 A s f x) = (term341 A s f x).
Proof. exact (MK_COMB (@lem4291402 A s f x) (@lem4291409 A f x)). Qed.
Lemma lem4291413 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term342 A s f x) = (term343 A s f x).
Proof. exact (MK_COMB (@lem4291361 A s f x) (@lem4291410 A s f x)). Qed.
Lemma lem4291416 {A : Type'} (s : A -> Prop) (f : A -> A) : (term344 A s f) = (term345 A s f).
Proof. exact (fun_ext (fun x : A => @lem4291413 A s f x)). Qed.
Lemma lem4291417 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4291418 {A : Type'} (s : A -> Prop) (f : A -> A) : (term303 A s f) = (term346 A s f).
Proof. exact (MK_COMB (@lem4291417 A) (@lem4291416 A s f)). Qed.
Lemma lem4291423 {A : Type'} (s : A -> Prop) (f : A -> A) : (term347 A s f) = (term348 A s f).
Proof. exact (MK_COMB (@lem4291316 A f s) (@lem4291418 A s f)). Qed.
Lemma lem4291426 {A : Type'} (s : A -> Prop) (f : A -> A) : (term348 A s f) = (term347 A s f).
Proof. exact (SYM (@lem4291423 A s f)). Qed.
Lemma lem4291428 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4291429 {A : Type'} (s : A -> Prop) (f : A -> A) : (term348 A s f) = (term349 A s f).
Proof. exact (@lem4291428 (term348 A s f)). Qed.
Lemma lem4291430 {A : Type'} (s : A -> Prop) (f : A -> A) : (term349 A s f) = (term348 A s f).
Proof. exact (SYM (@lem4291429 A s f)). Qed.
Lemma lem4291431 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term350 A s f) : term350 A s f.
Proof. exact (h1). Qed.
Lemma lem4291434 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term349 A s f) : term349 A s f.
Proof. exact (h1). Qed.
Lemma lem4291435 {A : Type'} (s : A -> Prop) (f : A -> A) : term351 A s f.
Proof. exact (fun h0 : term349 A s f => @lem4291434 A s f h0). Qed.
Lemma lem4291436 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term351 A s f) : term351 A s f.
Proof. exact (h1). Qed.
Lemma lem4291437 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term349 A s f) : term349 A s f.
Proof. exact (h1). Qed.
Lemma lem4291438 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term349 A s f) (h2 : term351 A s f) : term349 A s f.
Proof. exact (@lem4291436 A s f h2 (@lem4291437 A s f h1)). Qed.
Lemma lem4291439 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term349 A s f) : term352 A s f.
Proof. exact (fun h0 : term351 A s f => @lem4291438 A s f h1 h0). Qed.
Lemma lem4291440 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term351 A s f) : term351 A s f.
Proof. exact (h1). Qed.
Lemma lem4291441 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term349 A s f) (h2 : term351 A s f) : term349 A s f.
Proof. exact (@lem4291439 A s f h1 (@lem4291440 A s f h2)). Qed.
Lemma lem4291442 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term351 A s f) : term351 A s f.
Proof. exact (fun h0 : term349 A s f => @lem4291441 A s f h0 h1). Qed.
Lemma lem4291443 {A : Type'} (s : A -> Prop) (f : A -> A) : term353 A s f.
Proof. exact (fun h0 : term351 A s f => @lem4291442 A s f h0). Qed.
Lemma lem4291446 {A : Type'} (s : A -> Prop) (f : A -> A) : term351 A s f.
Proof. exact (@lem4291443 A s f (@lem4291435 A s f)). Qed.
Lemma lem4291447 {A : Type'} (s : A -> Prop) (f : A -> A) : term351 A s f.
Proof. exact (@lem4291446 A s f). Qed.
Lemma lem4291457 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4291458 {A : Type'} (s : A -> Prop) (f : A -> A) : (term349 A s f) = (term354 A s f).
Proof. exact (@lem4291457 (term350 A s f)). Qed.
Lemma lem4291460 (t : Prop) : (term24 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4291461 {A : Type'} (s : A -> Prop) (f : A -> A) : (term354 A s f) = (term348 A s f).
Proof. exact (@lem4291460 (term348 A s f)). Qed.
Lemma lem4291464 {A : Type'} (s : A -> Prop) (f : A -> A) : (term349 A s f) = (term348 A s f).
Proof. exact (TRANS (@lem4291458 A s f) (@lem4291461 A s f)). Qed.
Lemma lem4291489 {A : Type'} (f : A -> A) : (term355 A f) = (term356 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4291464 A s f)). Qed.
Lemma lem4291490 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4291491 {A : Type'} (f : A -> A) : (term357 A f) = (term358 A f).
Proof. exact (MK_COMB (@lem4291490 A) (@lem4291489 A f)). Qed.
Lemma lem4291496 {A : Type'} : (term359 A) = (term360 A).
Proof. exact (fun_ext (fun f : A -> A => @lem4291491 A f)). Qed.
Lemma lem4291497 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4291506 {A : Type'} : (term361 A) = (term362 A).
Proof. exact (MK_COMB (@lem4291497 A) (@lem4291496 A)). Qed.
Lemma lem4291533 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term343 A s f x) = (term343 A s f x).
Proof. exact (eq_refl (term343 A s f x)). Qed.
Lemma lem4291534 {A : Type'} (s : A -> Prop) (f : A -> A) : (term345 A s f) = (term345 A s f).
Proof. exact (fun_ext (fun x : A => @lem4291533 A s f x)). Qed.
Lemma lem4291535 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4291536 {A : Type'} (s : A -> Prop) (f : A -> A) : (term346 A s f) = (term346 A s f).
Proof. exact (MK_COMB (@lem4291535 A) (@lem4291534 A s f)). Qed.
Lemma lem4291537 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem4291546 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term317 A s f x) = (term317 A s f x).
Proof. exact (eq_refl (term317 A s f x)). Qed.
Lemma lem4291547 {A : Type'} (s : A -> Prop) (f : A -> A) : (term319 A s f) = (term319 A s f).
Proof. exact (fun_ext (fun x : A => @lem4291546 A s f x)). Qed.
Lemma lem4291548 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4291549 {A : Type'} (s : A -> Prop) (f : A -> A) : (term320 A s f) = (term320 A s f).
Proof. exact (MK_COMB (@lem4291548 A) (@lem4291547 A s f)). Qed.
Lemma lem4291550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291551 {A : Type'} (s : A -> Prop) (f : A -> A) : (term322 A s f) = (term322 A s f).
Proof. exact (MK_COMB (@lem4291550) (@lem4291549 A s f)). Qed.
Lemma lem4291552 {A : Type'} (f : A -> A) (s : A -> Prop) : (term323 A f s) = (term323 A f s).
Proof. exact (MK_COMB (@lem4291551 A s f) (@lem4291537 A s)). Qed.
Lemma lem4291553 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4291554 {A : Type'} (f : A -> A) (s : A -> Prop) : (term325 A f s) = (term325 A f s).
Proof. exact (MK_COMB (@lem4291553) (@lem4291552 A f s)). Qed.
Lemma lem4291555 {A : Type'} (s : A -> Prop) (f : A -> A) : (term348 A s f) = (term348 A s f).
Proof. exact (MK_COMB (@lem4291554 A f s) (@lem4291536 A s f)). Qed.
Lemma lem4291556 {A : Type'} (f : A -> A) : (term356 A f) = (term356 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4291555 A s f)). Qed.
Lemma lem4291557 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4291558 {A : Type'} (f : A -> A) : (term358 A f) = (term358 A f).
Proof. exact (MK_COMB (@lem4291557 A) (@lem4291556 A f)). Qed.
Lemma lem4291559 {A : Type'} : (term360 A) = (term360 A).
Proof. exact (fun_ext (fun f : A -> A => @lem4291558 A f)). Qed.
Lemma lem4291560 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4291561 {A : Type'} : (term362 A) = (term362 A).
Proof. exact (MK_COMB (@lem4291560 A) (@lem4291559 A)). Qed.
Lemma lem4291606 {A : Type'} : (term361 A) = (term362 A).
Proof. exact (TRANS (@lem4291506 A) (@lem4291561 A)). Qed.
Lemma lem4291607 {A : Type'} : (term362 A) = (term361 A).
Proof. exact (SYM (@lem4291606 A)). Qed.
Lemma lem4291608 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term323 A f s.
Proof. exact (h1). Qed.
Lemma lem4291611 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4291612 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term341 A s f x) = (term363 A s f x).
Proof. exact (@lem4291611 (term341 A s f x)). Qed.
Lemma lem4291613 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term363 A s f x) = (term341 A s f x).
Proof. exact (SYM (@lem4291612 A s f x)). Qed.
Lemma lem4291614 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term364 A s f x) : term364 A s f x.
Proof. exact (h1). Qed.
Lemma lem4291625 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term317 A s f x) = (term365 A s f x).
Proof. exact (@lem17265 (s x) (term315 A s f x)). Qed.
Lemma lem4291626 {A : Type'} (s : A -> Prop) (f : A -> A) : (term319 A s f) = (term366 A s f).
Proof. exact (fun_ext (fun x : A => @lem4291625 A s f x)). Qed.
Lemma lem4291627 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4291628 {A : Type'} (s : A -> Prop) (f : A -> A) : (term320 A s f) = (term367 A s f).
Proof. exact (MK_COMB (@lem4291627 A) (@lem4291626 A s f)). Qed.
Lemma lem4291629 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem4291630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291631 {A : Type'} (s : A -> Prop) (f : A -> A) : (term322 A s f) = (term368 A s f).
Proof. exact (MK_COMB (@lem4291630) (@lem4291628 A s f)). Qed.
Lemma lem4291684 {A : Type'} (f : A -> A) (s : A -> Prop) : (term323 A f s) = (term369 A f s).
Proof. exact (MK_COMB (@lem4291631 A s f) (@lem4291629 A s)). Qed.
Lemma lem4291685 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term369 A f s.
Proof. exact (EQ_MP (@lem4291684 A f s) (@lem4291608 A f s h1)). Qed.
Lemma lem4291695 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term177 A s f x.
Proof. exact (h1). Qed.
Lemma lem4291699 {A : Type'} (f : A -> A) (x : A) : (term370 A f x) = ((term313 A f x) = (f x)).
Proof. exact (@lem16933 ((term313 A f x) = (f x))). Qed.
Lemma lem4291701 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term371 A s f x) = (term371 A s f x).
Proof. exact (eq_refl (term371 A s f x)). Qed.
Lemma lem4291702 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term372 A s f x) = (term373 A s f x).
Proof. exact (MK_COMB (@lem4291701 A s f x) (@lem4291699 A f x)). Qed.
Lemma lem4291703 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term374 A s f x) = (term372 A s f x).
Proof. exact (@lem17045 (term310 A s f x) (term335 A f x)). Qed.
Lemma lem4291704 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term374 A s f x) = (term373 A s f x).
Proof. exact (TRANS (@lem4291703 A s f x) (@lem4291702 A s f x)). Qed.
Lemma lem4291707 {A : Type'} (f : A -> A) (x : A) : (term202 A f x) = ((f x) = x).
Proof. exact (@lem16933 ((f x) = x)). Qed.
Lemma lem4291708 {A : Type'} (f : A -> A) (x : A) : (term375 A f x) = (term375 A f x).
Proof. exact (eq_refl (term375 A f x)). Qed.
Lemma lem4291709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4291710 {A : Type'} (f : A -> A) (x : A) : (term376 A f x) = (term377 A f x).
Proof. exact (MK_COMB (@lem4291709) (@lem4291707 A f x)). Qed.
Lemma lem4291711 {A : Type'} (f : A -> A) (x : A) : (term378 A f x) = (term379 A f x).
Proof. exact (MK_COMB (@lem4291710 A f x) (@lem4291708 A f x)). Qed.
Lemma lem4291712 {A : Type'} (f : A -> A) (x : A) : (term380 A f x) = (term378 A f x).
Proof. exact (@lem17045 (term176 A f x) ((term313 A f x) = x)). Qed.
Lemma lem4291713 {A : Type'} (f : A -> A) (x : A) : (term380 A f x) = (term379 A f x).
Proof. exact (TRANS (@lem4291712 A f x) (@lem4291711 A f x)). Qed.
Lemma lem4291714 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4291715 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term381 A s f x) = (term382 A s f x).
Proof. exact (MK_COMB (@lem4291714) (@lem4291704 A s f x)). Qed.
Lemma lem4291716 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term383 A s f x) = (term384 A s f x).
Proof. exact (MK_COMB (@lem4291715 A s f x) (@lem4291713 A f x)). Qed.
Lemma lem4291717 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term364 A s f x) = (term383 A s f x).
Proof. exact (@lem17045 (term336 A s f x) (term339 A f x)). Qed.
Lemma lem4291722 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term364 A s f x) = (term384 A s f x).
Proof. exact (TRANS (@lem4291717 A s f x) (@lem4291716 A s f x)). Qed.
Lemma lem4291723 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term364 A s f x) : term384 A s f x.
Proof. exact (EQ_MP (@lem4291722 A s f x) (@lem4291614 A s f x h1)). Qed.
Lemma lem4291726 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem4291735 {A : Type'} (f : A -> A) (x : A) : ((term313 A f x) = x) = ((term313 A f x) = x).
Proof. exact (eq_refl ((term313 A f x) = x)). Qed.
Lemma lem4291742 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4291743 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4291742 A Prop f x). Qed.
Lemma lem4291745 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term310 A s f x) = (term385 A s f x).
Proof. exact (@lem4291743 A s (f x)). Qed.
Lemma lem4291746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291747 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term312 A s f x) = (term386 A s f x).
Proof. exact (MK_COMB (@lem4291746) (@lem4291745 A s f x)). Qed.
Lemma lem4291748 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term315 A s f x) = (term387 A s f x).
Proof. exact (MK_COMB (@lem4291747 A s f x) (@lem4291735 A f x)). Qed.
Lemma lem4291749 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4291754 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4291755 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4291754 A Prop f x). Qed.
Lemma lem4291757 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4291755 A s x). Qed.
Lemma lem4291758 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term388 A s x).
Proof. exact (MK_COMB (@lem4291749) (@lem4291757 A s x)). Qed.
Lemma lem4291759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4291760 {A : Type'} (s : A -> Prop) (x : A) : (term203 A s x) = (term389 A s x).
Proof. exact (MK_COMB (@lem4291759) (@lem4291758 A s x)). Qed.
Lemma lem4291761 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term365 A s f x) = (term390 A s f x).
Proof. exact (MK_COMB (@lem4291760 A s x) (@lem4291748 A s f x)). Qed.
Lemma lem4291762 {A : Type'} (s : A -> Prop) (f : A -> A) : (term366 A s f) = (term391 A s f).
Proof. exact (fun_ext (fun x : A => @lem4291761 A s f x)). Qed.
Lemma lem4291763 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4291764 {A : Type'} (s : A -> Prop) (f : A -> A) : (term367 A s f) = (term392 A s f).
Proof. exact (MK_COMB (@lem4291763 A) (@lem4291762 A s f)). Qed.
Lemma lem4291765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291766 {A : Type'} (s : A -> Prop) (f : A -> A) : (term368 A s f) = (term393 A s f).
Proof. exact (MK_COMB (@lem4291765) (@lem4291764 A s f)). Qed.
Lemma lem4291767 {A : Type'} (f : A -> A) (s : A -> Prop) : (term369 A f s) = (term394 A f s).
Proof. exact (MK_COMB (@lem4291766 A s f) (@lem4291726 A s)). Qed.
Lemma lem4291768 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term394 A f s.
Proof. exact (EQ_MP (@lem4291767 A f s) (@lem4291685 A f s h1)). Qed.
Lemma lem4291777 {A : Type'} (f : A -> A) (x : A) : (term176 A f x) = (term176 A f x).
Proof. exact (eq_refl (term176 A f x)). Qed.
Lemma lem4291782 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4291783 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4291782 A Prop f x). Qed.
Lemma lem4291785 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4291783 A s x). Qed.
Lemma lem4291786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4291787 {A : Type'} (s : A -> Prop) (x : A) : (term55 A s x) = (term395 A s x).
Proof. exact (MK_COMB (@lem4291786) (@lem4291785 A s x)). Qed.
Lemma lem4291788 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term177 A s f x) = (term396 A s f x).
Proof. exact (MK_COMB (@lem4291787 A s x) (@lem4291777 A f x)). Qed.
Lemma lem4291789 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term396 A s f x.
Proof. exact (EQ_MP (@lem4291788 A s f x) (@lem4291695 A s f x h1)). Qed.
Lemma lem4291810 {A : Type'} (f : A -> A) (x : A) : (term379 A f x) = (term379 A f x).
Proof. exact (eq_refl (term379 A f x)). Qed.
Lemma lem4291821 {A : Type'} (f : A -> A) (x : A) : ((term313 A f x) = (f x)) = ((term313 A f x) = (f x)).
Proof. exact (eq_refl ((term313 A f x) = (f x))). Qed.
Lemma lem4291822 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4291829 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4291830 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4291829 A Prop f x). Qed.
Lemma lem4291832 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term310 A s f x) = (term385 A s f x).
Proof. exact (@lem4291830 A s (f x)). Qed.
Lemma lem4291833 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term397 A s f x) = (term398 A s f x).
Proof. exact (MK_COMB (@lem4291822) (@lem4291832 A s f x)). Qed.
Lemma lem4291834 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4291835 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term371 A s f x) = (term399 A s f x).
Proof. exact (MK_COMB (@lem4291834) (@lem4291833 A s f x)). Qed.
Lemma lem4291836 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term373 A s f x) = (term400 A s f x).
Proof. exact (MK_COMB (@lem4291835 A s f x) (@lem4291821 A f x)). Qed.
Lemma lem4291837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4291838 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term382 A s f x) = (term401 A s f x).
Proof. exact (MK_COMB (@lem4291837) (@lem4291836 A s f x)). Qed.
Lemma lem4291839 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term384 A s f x) = (term402 A s f x).
Proof. exact (MK_COMB (@lem4291838 A s f x) (@lem4291810 A f x)). Qed.
Lemma lem4291840 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term364 A s f x) : term402 A s f x.
Proof. exact (EQ_MP (@lem4291839 A s f x) (@lem4291723 A s f x h1)). Qed.
Lemma lem4291844 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term392 A s f.
Proof. exact (proj1 (@lem4291768 A f s h1)). Qed.
Lemma lem4291845 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term400 A s f x) : term400 A s f x.
Proof. exact (h1). Qed.
Lemma lem4291846 {A : Type'} (f : A -> A) (x : A) (h1 : term379 A f x) : term379 A f x.
Proof. exact (h1). Qed.
Lemma lem4291876 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term390 A s f x) = (term403 A s f x).
Proof. exact (@lem19490 (term385 A s f x) (term388 A s x) ((term313 A f x) = x)). Qed.
Lemma lem4291877 {A : Type'} (s : A -> Prop) (f : A -> A) : (term391 A s f) = (term404 A s f).
Proof. exact (fun_ext (fun x : A => @lem4291876 A s f x)). Qed.
Lemma lem4291878 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4291880 {A : Type'} (s : A -> Prop) (f : A -> A) : (term392 A s f) = (term405 A s f).
Proof. exact (MK_COMB (@lem4291878 A) (@lem4291877 A s f)). Qed.
Lemma lem4291881 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term405 A s f.
Proof. exact (EQ_MP (@lem4291880 A s f) (@lem4291844 A f s h1)). Qed.
Lemma lem4291889 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) : term398 A s f x.
Proof. exact (h1). Qed.
Lemma lem4291915 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term390 A s f x) = (term403 A s f x).
Proof. exact (@lem19490 (term385 A s f x) (term388 A s x) ((term313 A f x) = x)). Qed.
Lemma lem4291916 {A : Type'} (s : A -> Prop) (f : A -> A) : (term391 A s f) = (term404 A s f).
Proof. exact (fun_ext (fun x : A => @lem4291915 A s f x)). Qed.
Lemma lem4291917 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4291919 {A : Type'} (s : A -> Prop) (f : A -> A) : (term392 A s f) = (term405 A s f).
Proof. exact (MK_COMB (@lem4291917 A) (@lem4291916 A s f)). Qed.
Lemma lem4291920 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term405 A s f.
Proof. exact (EQ_MP (@lem4291919 A s f) (@lem4291844 A f s h1)). Qed.
Lemma lem4291928 {A : Type'} (f : A -> A) (x : A) (h1 : (term313 A f x) = (f x)) : (term313 A f x) = (f x).
Proof. exact (h1). Qed.
Lemma lem4291967 {A : Type'} (f : A -> A) (x : A) (h1 : (f x) = x) : (f x) = x.
Proof. exact (h1). Qed.
Lemma lem4291993 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term390 A s f x) = (term403 A s f x).
Proof. exact (@lem19490 (term385 A s f x) (term388 A s x) ((term313 A f x) = x)). Qed.
Lemma lem4291994 {A : Type'} (s : A -> Prop) (f : A -> A) : (term391 A s f) = (term404 A s f).
Proof. exact (fun_ext (fun x : A => @lem4291993 A s f x)). Qed.
Lemma lem4291995 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4291997 {A : Type'} (s : A -> Prop) (f : A -> A) : (term392 A s f) = (term405 A s f).
Proof. exact (MK_COMB (@lem4291995 A) (@lem4291994 A s f)). Qed.
Lemma lem4291998 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term405 A s f.
Proof. exact (EQ_MP (@lem4291997 A s f) (@lem4291844 A f s h1)). Qed.
Lemma lem4292006 {A : Type'} (f : A -> A) (x : A) (h1 : term375 A f x) : term375 A f x.
Proof. exact (h1). Qed.
Lemma lem4292007 {A : Type'} (_48644 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term406 A s f _48644.
Proof. exact (@lem4291881 A f s h1 _48644). Qed.
Lemma lem4292008 {A : Type'} (s : A -> Prop) (f : A -> A) (_48644 : A) : (term406 A s f _48644) = (term403 A s f _48644).
Proof. exact (eq_refl (term406 A s f _48644)). Qed.
Lemma lem4292009 {A : Type'} (_48644 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term403 A s f _48644.
Proof. exact (EQ_MP (@lem4292008 A s f _48644) (@lem4292007 A _48644 f s h1)). Qed.
Lemma lem4292010 {A : Type'} (_48645 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term406 A s f _48645.
Proof. exact (@lem4291920 A f s h1 _48645). Qed.
Lemma lem4292011 {A : Type'} (s : A -> Prop) (f : A -> A) (_48645 : A) : (term406 A s f _48645) = (term403 A s f _48645).
Proof. exact (eq_refl (term406 A s f _48645)). Qed.
Lemma lem4292012 {A : Type'} (_48645 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term403 A s f _48645.
Proof. exact (EQ_MP (@lem4292011 A s f _48645) (@lem4292010 A _48645 f s h1)). Qed.
Lemma lem4292016 {A : Type'} (_48647 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term406 A s f _48647.
Proof. exact (@lem4291998 A f s h1 _48647). Qed.
Lemma lem4292017 {A : Type'} (s : A -> Prop) (f : A -> A) (_48647 : A) : (term406 A s f _48647) = (term403 A s f _48647).
Proof. exact (eq_refl (term406 A s f _48647)). Qed.
Lemma lem4292018 {A : Type'} (_48647 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term403 A s f _48647.
Proof. exact (EQ_MP (@lem4292017 A s f _48647) (@lem4292016 A _48647 f s h1)). Qed.
Lemma lem4292034 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) : term398 A s f x.
Proof. exact (h1). Qed.
Lemma lem4292040 {A : Type'} (_48644 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term407 A s f _48644.
Proof. exact (proj1 (@lem4292009 A _48644 f s h1)). Qed.
Lemma lem4292050 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term176 A f x.
Proof. exact (proj2 (@lem4291789 A s f x h1)). Qed.
Lemma lem4292054 {A : Type'} (f : A -> A) (x : A) (h1 : (term313 A f x) = (f x)) : (term313 A f x) = (f x).
Proof. exact (h1). Qed.
Lemma lem4292066 {A : Type'} (_48645 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term408 A s f _48645.
Proof. exact (proj2 (@lem4292012 A _48645 f s h1)). Qed.
Lemma lem4292070 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term176 A f x.
Proof. exact (proj2 (@lem4291789 A s f x h1)). Qed.
Lemma lem4292074 {A : Type'} (f : A -> A) (x : A) (h1 : (f x) = x) : (f x) = x.
Proof. exact (h1). Qed.
Lemma lem4292094 {A : Type'} (f : A -> A) (x : A) (h1 : term375 A f x) : term375 A f x.
Proof. exact (h1). Qed.
Lemma lem4292106 {A : Type'} (_48647 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term408 A s f _48647.
Proof. exact (proj2 (@lem4292018 A _48647 f s h1)). Qed.
Lemma lem4292151 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem4291789 A s f x h1)). Qed.
Lemma lem4292152 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term409 A s x.
Proof. exact (fun h0 : term388 A s x => @lem4292151 A s f x h1). Qed.
Lemma lem4292154 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292155 {A : Type'} (s : A -> Prop) (x : A) : (term409 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4292154 (@I (A -> Prop) s x)). Qed.
Lemma lem4292156 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4292155 A s x) (@lem4292152 A s f x h1)). Qed.
Lemma lem4292162 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4292163 {A : Type'} (f : A -> A) (s : A -> Prop) (_48644 : A) : (term407 A s f _48644) = (term410 A f s _48644).
Proof. exact (@lem4292162 (term385 A s f _48644) (term388 A s _48644)). Qed.
Lemma lem4292169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4292170 {A : Type'} (f : A -> A) (s : A -> Prop) (_48644 : A) : (term411 A s f _48644) = (term412 A f s _48644).
Proof. exact (MK_COMB (@lem4292169) (@lem4292163 A f s _48644)). Qed.
Lemma lem4292176 {A : Type'} (f : A -> A) (s : A -> Prop) (_48644 : A) : (term410 A f s _48644) = (term410 A f s _48644).
Proof. exact (eq_refl (term410 A f s _48644)). Qed.
Lemma lem4292177 {A : Type'} (f : A -> A) (s : A -> Prop) (_48644 : A) : ((term407 A s f _48644) = (term410 A f s _48644)) = ((term410 A f s _48644) = (term410 A f s _48644)).
Proof. exact (MK_COMB (@lem4292170 A f s _48644) (@lem4292176 A f s _48644)). Qed.
Lemma lem4292179 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4292180 (x : Prop) : (x = x) = True.
Proof. exact (@lem4292179 Prop x). Qed.
Lemma lem4292181 {A : Type'} (f : A -> A) (s : A -> Prop) (_48644 : A) : ((term410 A f s _48644) = (term410 A f s _48644)) = True.
Proof. exact (@lem4292180 (term410 A f s _48644)). Qed.
Lemma lem4292182 {A : Type'} (f : A -> A) (s : A -> Prop) (_48644 : A) : ((term407 A s f _48644) = (term410 A f s _48644)) = True.
Proof. exact (TRANS (@lem4292177 A f s _48644) (@lem4292181 A f s _48644)). Qed.
Lemma lem4292183 {A : Type'} (f : A -> A) (s : A -> Prop) (_48644 : A) : True = ((term407 A s f _48644) = (term410 A f s _48644)).
Proof. exact (SYM (@lem4292182 A f s _48644)). Qed.
Lemma lem4292184 {A : Type'} (f : A -> A) (s : A -> Prop) (_48644 : A) : (term407 A s f _48644) = (term410 A f s _48644).
Proof. exact (EQ_MP (@lem4292183 A f s _48644) (@lem0)). Qed.
Lemma lem4292185 {A : Type'} (_48644 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term410 A f s _48644.
Proof. exact (EQ_MP (@lem4292184 A f s _48644) (@lem4292040 A _48644 f s h1)). Qed.
Lemma lem4292187 (b : Prop) (a : Prop) : (a \/ b) = (term413 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4292188 {A : Type'} (s : A -> Prop) (f : A -> A) (_48644 : A) : (term410 A f s _48644) = (term414 A s f _48644).
Proof. exact (@lem4292187 (term388 A s _48644) (term385 A s f _48644)). Qed.
Lemma lem4292190 (a : Prop) : (term24 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4292191 {A : Type'} (s : A -> Prop) (_48644 : A) : (term415 A s _48644) = (@I (A -> Prop) s _48644).
Proof. exact (@lem4292190 (@I (A -> Prop) s _48644)). Qed.
Lemma lem4292192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4292193 {A : Type'} (s : A -> Prop) (_48644 : A) : (term416 A s _48644) = (term417 A s _48644).
Proof. exact (MK_COMB (@lem4292192) (@lem4292191 A s _48644)). Qed.
Lemma lem4292194 {A : Type'} (s : A -> Prop) (f : A -> A) (_48644 : A) : (term385 A s f _48644) = (term385 A s f _48644).
Proof. exact (eq_refl (term385 A s f _48644)). Qed.
Lemma lem4292195 {A : Type'} (s : A -> Prop) (f : A -> A) (_48644 : A) : (term414 A s f _48644) = (term418 A s f _48644).
Proof. exact (MK_COMB (@lem4292193 A s _48644) (@lem4292194 A s f _48644)). Qed.
Lemma lem4292196 {A : Type'} (s : A -> Prop) (f : A -> A) (_48644 : A) : (term410 A f s _48644) = (term418 A s f _48644).
Proof. exact (TRANS (@lem4292188 A s f _48644) (@lem4292195 A s f _48644)). Qed.
Lemma lem4292199 {A : Type'} (_48644 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term418 A s f _48644.
Proof. exact (EQ_MP (@lem4292196 A s f _48644) (@lem4292185 A _48644 f s h1)). Qed.
Lemma lem4292200 {A : Type'} (_48644 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term418 A s f _48644.
Proof. exact (@lem4292199 A _48644 f s h1). Qed.
Lemma lem4292201 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term418 A s f x.
Proof. exact (@lem4292200 A x f s h1). Qed.
Lemma lem4292204 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : term385 A s f x.
Proof. exact (@lem4292201 A x f s h1 (@lem4292156 A s f x h2)). Qed.
Lemma lem4292205 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : term419 A s f x.
Proof. exact (fun h0 : term398 A s f x => @lem4292204 A s f x h1 h2). Qed.
Lemma lem4292207 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292208 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term419 A s f x) = (term385 A s f x).
Proof. exact (@lem4292207 (term385 A s f x)). Qed.
Lemma lem4292209 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : term385 A s f x.
Proof. exact (EQ_MP (@lem4292208 A s f x) (@lem4292205 A s f x h1 h2)). Qed.
Lemma lem4292212 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4292214 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term398 A s f x) = (term420 A s f x).
Proof. exact (@lem4292212 (term385 A s f x)). Qed.
Lemma lem4292217 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) : term420 A s f x.
Proof. exact (EQ_MP (@lem4292214 A s f x) (@lem4292034 A s f x h1)). Qed.
Lemma lem4292220 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (@lem4292217 A s f x h1 (@lem4292209 A s f x h2 h3)). Qed.
Lemma lem4292221 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : term104.
Proof. exact (fun h0 : ~ False => @lem4292220 A s f x h1 h2 h3). Qed.
Lemma lem4292223 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292224 : term104 = False.
Proof. exact (@lem4292223 False). Qed.
Lemma lem4292225 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (EQ_MP (@lem4292224) (@lem4292221 A s f x h1 h2 h3)). Qed.
Lemma lem4292266 {A : Type'} (x : A) (y : A) (z : A) : term421 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem4292270 {A : Type'} (f : A -> A) (x : A) (h1 : (term313 A f x) = (f x)) : (term313 A f x) = (f x).
Proof. exact (h1). Qed.
Lemma lem4292271 {A : Type'} (f : A -> A) (x : A) (h1 : (term313 A f x) = (f x)) : term422 A f x.
Proof. exact (fun h0 : term335 A f x => @lem4292270 A f x h1). Qed.
Lemma lem4292273 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292274 {A : Type'} (f : A -> A) (x : A) : (term422 A f x) = ((term313 A f x) = (f x)).
Proof. exact (@lem4292273 ((term313 A f x) = (f x))). Qed.
Lemma lem4292275 {A : Type'} (f : A -> A) (x : A) (h1 : (term313 A f x) = (f x)) : (term313 A f x) = (f x).
Proof. exact (EQ_MP (@lem4292274 A f x) (@lem4292271 A f x h1)). Qed.
Lemma lem4292277 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem4291789 A s f x h1)). Qed.
Lemma lem4292278 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term409 A s x.
Proof. exact (fun h0 : term388 A s x => @lem4292277 A s f x h1). Qed.
Lemma lem4292280 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292281 {A : Type'} (s : A -> Prop) (x : A) : (term409 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4292280 (@I (A -> Prop) s x)). Qed.
Lemma lem4292282 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4292281 A s x) (@lem4292278 A s f x h1)). Qed.
Lemma lem4292288 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4292289 {A : Type'} (f : A -> A) (s : A -> Prop) (_48645 : A) : (term408 A s f _48645) = (term423 A f s _48645).
Proof. exact (@lem4292288 ((term313 A f _48645) = _48645) (term388 A s _48645)). Qed.
Lemma lem4292297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4292298 {A : Type'} (f : A -> A) (s : A -> Prop) (_48645 : A) : (term424 A s f _48645) = (term425 A f s _48645).
Proof. exact (MK_COMB (@lem4292297) (@lem4292289 A f s _48645)). Qed.
Lemma lem4292306 {A : Type'} (f : A -> A) (s : A -> Prop) (_48645 : A) : (term423 A f s _48645) = (term423 A f s _48645).
Proof. exact (eq_refl (term423 A f s _48645)). Qed.
Lemma lem4292307 {A : Type'} (f : A -> A) (s : A -> Prop) (_48645 : A) : ((term408 A s f _48645) = (term423 A f s _48645)) = ((term423 A f s _48645) = (term423 A f s _48645)).
Proof. exact (MK_COMB (@lem4292298 A f s _48645) (@lem4292306 A f s _48645)). Qed.
Lemma lem4292309 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4292310 (x : Prop) : (x = x) = True.
Proof. exact (@lem4292309 Prop x). Qed.
Lemma lem4292311 {A : Type'} (f : A -> A) (s : A -> Prop) (_48645 : A) : ((term423 A f s _48645) = (term423 A f s _48645)) = True.
Proof. exact (@lem4292310 (term423 A f s _48645)). Qed.
Lemma lem4292312 {A : Type'} (f : A -> A) (s : A -> Prop) (_48645 : A) : ((term408 A s f _48645) = (term423 A f s _48645)) = True.
Proof. exact (TRANS (@lem4292307 A f s _48645) (@lem4292311 A f s _48645)). Qed.
Lemma lem4292313 {A : Type'} (f : A -> A) (s : A -> Prop) (_48645 : A) : True = ((term408 A s f _48645) = (term423 A f s _48645)).
Proof. exact (SYM (@lem4292312 A f s _48645)). Qed.
Lemma lem4292314 {A : Type'} (f : A -> A) (s : A -> Prop) (_48645 : A) : (term408 A s f _48645) = (term423 A f s _48645).
Proof. exact (EQ_MP (@lem4292313 A f s _48645) (@lem0)). Qed.
Lemma lem4292315 {A : Type'} (_48645 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term423 A f s _48645.
Proof. exact (EQ_MP (@lem4292314 A f s _48645) (@lem4292066 A _48645 f s h1)). Qed.
Lemma lem4292317 (b : Prop) (a : Prop) : (a \/ b) = (term413 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4292318 {A : Type'} (s : A -> Prop) (f : A -> A) (_48645 : A) : (term423 A f s _48645) = (term426 A s f _48645).
Proof. exact (@lem4292317 (term388 A s _48645) ((term313 A f _48645) = _48645)). Qed.
Lemma lem4292320 (a : Prop) : (term24 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4292321 {A : Type'} (s : A -> Prop) (_48645 : A) : (term415 A s _48645) = (@I (A -> Prop) s _48645).
Proof. exact (@lem4292320 (@I (A -> Prop) s _48645)). Qed.
Lemma lem4292322 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4292323 {A : Type'} (s : A -> Prop) (_48645 : A) : (term416 A s _48645) = (term417 A s _48645).
Proof. exact (MK_COMB (@lem4292322) (@lem4292321 A s _48645)). Qed.
Lemma lem4292324 {A : Type'} (f : A -> A) (_48645 : A) : ((term313 A f _48645) = _48645) = ((term313 A f _48645) = _48645).
Proof. exact (eq_refl ((term313 A f _48645) = _48645)). Qed.
Lemma lem4292325 {A : Type'} (s : A -> Prop) (f : A -> A) (_48645 : A) : (term426 A s f _48645) = (term427 A s f _48645).
Proof. exact (MK_COMB (@lem4292323 A s _48645) (@lem4292324 A f _48645)). Qed.
Lemma lem4292326 {A : Type'} (s : A -> Prop) (f : A -> A) (_48645 : A) : (term423 A f s _48645) = (term427 A s f _48645).
Proof. exact (TRANS (@lem4292318 A s f _48645) (@lem4292325 A s f _48645)). Qed.
Lemma lem4292329 {A : Type'} (_48645 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term427 A s f _48645.
Proof. exact (EQ_MP (@lem4292326 A s f _48645) (@lem4292315 A _48645 f s h1)). Qed.
Lemma lem4292330 {A : Type'} (_48645 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term427 A s f _48645.
Proof. exact (@lem4292329 A _48645 f s h1). Qed.
Lemma lem4292331 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term427 A s f x.
Proof. exact (@lem4292330 A x f s h1). Qed.
Lemma lem4292334 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : (term313 A f x) = x.
Proof. exact (@lem4292331 A x f s h1 (@lem4292282 A s f x h2)). Qed.
Lemma lem4292335 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : term428 A f x.
Proof. exact (fun h0 : term375 A f x => @lem4292334 A s f x h1 h2). Qed.
Lemma lem4292337 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292338 {A : Type'} (f : A -> A) (x : A) : (term428 A f x) = ((term313 A f x) = x).
Proof. exact (@lem4292337 ((term313 A f x) = x)). Qed.
Lemma lem4292339 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : (term313 A f x) = x.
Proof. exact (EQ_MP (@lem4292338 A f x) (@lem4292335 A s f x h1 h2)). Qed.
Lemma lem4292357 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4292358 {A : Type'} (y : A) (x : A) (z : A) : (term429 A x y z) = (term430 A y x z).
Proof. exact (@lem4292357 (y = z) (term431 A x z)). Qed.
Lemma lem4292368 {A : Type'} (x : A) (y : A) : (term432 A x y) = (term432 A x y).
Proof. exact (eq_refl (term432 A x y)). Qed.
Lemma lem4292369 {A : Type'} (y : A) (x : A) (z : A) : (term421 A x y z) = (term433 A y x z).
Proof. exact (MK_COMB (@lem4292368 A x y) (@lem4292358 A y x z)). Qed.
Lemma lem4292373 (q : Prop) (p : Prop) (r : Prop) : (term434 p q r) = (term434 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4292374 {A : Type'} (y : A) (x : A) (z : A) : (term433 A y x z) = (term435 A y x z).
Proof. exact (@lem4292373 (y = z) (term431 A x y) (term431 A x z)). Qed.
Lemma lem4292396 {A : Type'} (y : A) (x : A) (z : A) : (term421 A x y z) = (term435 A y x z).
Proof. exact (TRANS (@lem4292369 A y x z) (@lem4292374 A y x z)). Qed.
Lemma lem4292397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4292398 {A : Type'} (y : A) (x : A) (z : A) : (term436 A x y z) = (term437 A y x z).
Proof. exact (MK_COMB (@lem4292397) (@lem4292396 A y x z)). Qed.
Lemma lem4292420 {A : Type'} (y : A) (x : A) (z : A) : (term435 A y x z) = (term435 A y x z).
Proof. exact (eq_refl (term435 A y x z)). Qed.
Lemma lem4292421 {A : Type'} (y : A) (x : A) (z : A) : ((term421 A x y z) = (term435 A y x z)) = ((term435 A y x z) = (term435 A y x z)).
Proof. exact (MK_COMB (@lem4292398 A y x z) (@lem4292420 A y x z)). Qed.
Lemma lem4292423 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4292424 (x : Prop) : (x = x) = True.
Proof. exact (@lem4292423 Prop x). Qed.
Lemma lem4292425 {A : Type'} (y : A) (x : A) (z : A) : ((term435 A y x z) = (term435 A y x z)) = True.
Proof. exact (@lem4292424 (term435 A y x z)). Qed.
Lemma lem4292426 {A : Type'} (y : A) (x : A) (z : A) : ((term421 A x y z) = (term435 A y x z)) = True.
Proof. exact (TRANS (@lem4292421 A y x z) (@lem4292425 A y x z)). Qed.
Lemma lem4292427 {A : Type'} (y : A) (x : A) (z : A) : True = ((term421 A x y z) = (term435 A y x z)).
Proof. exact (SYM (@lem4292426 A y x z)). Qed.
Lemma lem4292428 {A : Type'} (y : A) (x : A) (z : A) : (term421 A x y z) = (term435 A y x z).
Proof. exact (EQ_MP (@lem4292427 A y x z) (@lem0)). Qed.
Lemma lem4292429 {A : Type'} (y : A) (x : A) (z : A) : term435 A y x z.
Proof. exact (EQ_MP (@lem4292428 A y x z) (@lem4292266 A x y z)). Qed.
Lemma lem4292431 (b : Prop) (a : Prop) : (a \/ b) = (term413 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4292432 {A : Type'} (x : A) (y : A) (z : A) : (term435 A y x z) = (term438 A x y z).
Proof. exact (@lem4292431 (term439 A y x z) (y = z)). Qed.
Lemma lem4292434 (a : Prop) (b : Prop) : (term440 a b) = (term441 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4292435 {A : Type'} (y : A) (x : A) (z : A) : (term442 A y x z) = (term443 A y x z).
Proof. exact (@lem4292434 (term431 A x y) (term431 A x z)). Qed.
Lemma lem4292437 (a : Prop) : (term24 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4292438 {A : Type'} (x : A) (y : A) : (term444 A x y) = (x = y).
Proof. exact (@lem4292437 (x = y)). Qed.
Lemma lem4292439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4292440 {A : Type'} (x : A) (y : A) : (term445 A x y) = (term446 A x y).
Proof. exact (MK_COMB (@lem4292439) (@lem4292438 A x y)). Qed.
Lemma lem4292442 (a : Prop) : (term24 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4292443 {A : Type'} (x : A) (z : A) : (term444 A x z) = (x = z).
Proof. exact (@lem4292442 (x = z)). Qed.
Lemma lem4292444 {A : Type'} (y : A) (x : A) (z : A) : (term443 A y x z) = (term447 A y x z).
Proof. exact (MK_COMB (@lem4292440 A x y) (@lem4292443 A x z)). Qed.
Lemma lem4292445 {A : Type'} (y : A) (x : A) (z : A) : (term442 A y x z) = (term447 A y x z).
Proof. exact (TRANS (@lem4292435 A y x z) (@lem4292444 A y x z)). Qed.
Lemma lem4292446 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4292447 {A : Type'} (y : A) (x : A) (z : A) : (term448 A y x z) = (term449 A y x z).
Proof. exact (MK_COMB (@lem4292446) (@lem4292445 A y x z)). Qed.
Lemma lem4292448 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4292449 {A : Type'} (x : A) (y : A) (z : A) : (term438 A x y z) = (term450 A x y z).
Proof. exact (MK_COMB (@lem4292447 A y x z) (@lem4292448 A y z)). Qed.
Lemma lem4292450 {A : Type'} (x : A) (y : A) (z : A) : (term435 A y x z) = (term450 A x y z).
Proof. exact (TRANS (@lem4292432 A x y z) (@lem4292449 A x y z)). Qed.
Lemma lem4292452 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : term451 A f x.
Proof. exact (conj (@lem4292275 A f x h3) (@lem4292339 A s f x h1 h2)). Qed.
Lemma lem4292454 {A : Type'} (x : A) (y : A) (z : A) : term450 A x y z.
Proof. exact (EQ_MP (@lem4292450 A x y z) (@lem4292429 A y x z)). Qed.
Lemma lem4292455 {A : Type'} (x : A) (y : A) (z : A) : term450 A x y z.
Proof. exact (@lem4292454 A x y z). Qed.
Lemma lem4292456 {A : Type'} (f : A -> A) (x : A) : term452 A f x.
Proof. exact (@lem4292455 A (term313 A f x) (f x) x). Qed.
Lemma lem4292459 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : (f x) = x.
Proof. exact (@lem4292456 A f x (@lem4292452 A s f x h1 h2 h3)). Qed.
Lemma lem4292460 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : term220 A f x.
Proof. exact (fun h0 : term176 A f x => @lem4292459 A s f x h1 h2 h3). Qed.
Lemma lem4292462 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292463 {A : Type'} (f : A -> A) (x : A) : (term220 A f x) = ((f x) = x).
Proof. exact (@lem4292462 ((f x) = x)). Qed.
Lemma lem4292464 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : (f x) = x.
Proof. exact (EQ_MP (@lem4292463 A f x) (@lem4292460 A s f x h1 h2 h3)). Qed.
Lemma lem4292467 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4292469 {A : Type'} (f : A -> A) (x : A) : (term176 A f x) = (term221 A f x).
Proof. exact (@lem4292467 ((f x) = x)). Qed.
Lemma lem4292472 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term221 A f x.
Proof. exact (EQ_MP (@lem4292469 A f x) (@lem4292050 A s f x h1)). Qed.
Lemma lem4292475 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : False.
Proof. exact (@lem4292472 A s f x h2 (@lem4292464 A s f x h1 h2 h3)). Qed.
Lemma lem4292476 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : term104.
Proof. exact (fun h0 : ~ False => @lem4292475 A s f x h1 h2 h3). Qed.
Lemma lem4292478 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292479 : term104 = False.
Proof. exact (@lem4292478 False). Qed.
Lemma lem4292480 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : False.
Proof. exact (EQ_MP (@lem4292479) (@lem4292476 A s f x h1 h2 h3)). Qed.
Lemma lem4292525 {A : Type'} (f : A -> A) (x : A) (h1 : (f x) = x) : (f x) = x.
Proof. exact (h1). Qed.
Lemma lem4292526 {A : Type'} (f : A -> A) (x : A) (h1 : (f x) = x) : term220 A f x.
Proof. exact (fun h0 : term176 A f x => @lem4292525 A f x h1). Qed.
Lemma lem4292528 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292529 {A : Type'} (f : A -> A) (x : A) : (term220 A f x) = ((f x) = x).
Proof. exact (@lem4292528 ((f x) = x)). Qed.
Lemma lem4292530 {A : Type'} (f : A -> A) (x : A) (h1 : (f x) = x) : (f x) = x.
Proof. exact (EQ_MP (@lem4292529 A f x) (@lem4292526 A f x h1)). Qed.
Lemma lem4292533 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4292535 {A : Type'} (f : A -> A) (x : A) : (term176 A f x) = (term221 A f x).
Proof. exact (@lem4292533 ((f x) = x)). Qed.
Lemma lem4292538 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term221 A f x.
Proof. exact (EQ_MP (@lem4292535 A f x) (@lem4292070 A s f x h1)). Qed.
Lemma lem4292541 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) (h2 : (f x) = x) : False.
Proof. exact (@lem4292538 A s f x h1 (@lem4292530 A f x h2)). Qed.
Lemma lem4292542 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) (h2 : (f x) = x) : term104.
Proof. exact (fun h0 : ~ False => @lem4292541 A s f x h1 h2). Qed.
Lemma lem4292544 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292545 : term104 = False.
Proof. exact (@lem4292544 False). Qed.
Lemma lem4292546 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4292545) (@lem4292542 A s f x h1 h2)). Qed.
Lemma lem4292591 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem4291789 A s f x h1)). Qed.
Lemma lem4292592 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : term409 A s x.
Proof. exact (fun h0 : term388 A s x => @lem4292591 A s f x h1). Qed.
Lemma lem4292594 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292595 {A : Type'} (s : A -> Prop) (x : A) : (term409 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4292594 (@I (A -> Prop) s x)). Qed.
Lemma lem4292596 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4292595 A s x) (@lem4292592 A s f x h1)). Qed.
Lemma lem4292602 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4292603 {A : Type'} (f : A -> A) (s : A -> Prop) (_48647 : A) : (term408 A s f _48647) = (term423 A f s _48647).
Proof. exact (@lem4292602 ((term313 A f _48647) = _48647) (term388 A s _48647)). Qed.
Lemma lem4292611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4292612 {A : Type'} (f : A -> A) (s : A -> Prop) (_48647 : A) : (term424 A s f _48647) = (term425 A f s _48647).
Proof. exact (MK_COMB (@lem4292611) (@lem4292603 A f s _48647)). Qed.
Lemma lem4292620 {A : Type'} (f : A -> A) (s : A -> Prop) (_48647 : A) : (term423 A f s _48647) = (term423 A f s _48647).
Proof. exact (eq_refl (term423 A f s _48647)). Qed.
Lemma lem4292621 {A : Type'} (f : A -> A) (s : A -> Prop) (_48647 : A) : ((term408 A s f _48647) = (term423 A f s _48647)) = ((term423 A f s _48647) = (term423 A f s _48647)).
Proof. exact (MK_COMB (@lem4292612 A f s _48647) (@lem4292620 A f s _48647)). Qed.
Lemma lem4292623 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4292624 (x : Prop) : (x = x) = True.
Proof. exact (@lem4292623 Prop x). Qed.
Lemma lem4292625 {A : Type'} (f : A -> A) (s : A -> Prop) (_48647 : A) : ((term423 A f s _48647) = (term423 A f s _48647)) = True.
Proof. exact (@lem4292624 (term423 A f s _48647)). Qed.
Lemma lem4292626 {A : Type'} (f : A -> A) (s : A -> Prop) (_48647 : A) : ((term408 A s f _48647) = (term423 A f s _48647)) = True.
Proof. exact (TRANS (@lem4292621 A f s _48647) (@lem4292625 A f s _48647)). Qed.
Lemma lem4292627 {A : Type'} (f : A -> A) (s : A -> Prop) (_48647 : A) : True = ((term408 A s f _48647) = (term423 A f s _48647)).
Proof. exact (SYM (@lem4292626 A f s _48647)). Qed.
Lemma lem4292628 {A : Type'} (f : A -> A) (s : A -> Prop) (_48647 : A) : (term408 A s f _48647) = (term423 A f s _48647).
Proof. exact (EQ_MP (@lem4292627 A f s _48647) (@lem0)). Qed.
Lemma lem4292629 {A : Type'} (_48647 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term423 A f s _48647.
Proof. exact (EQ_MP (@lem4292628 A f s _48647) (@lem4292106 A _48647 f s h1)). Qed.
Lemma lem4292631 (b : Prop) (a : Prop) : (a \/ b) = (term413 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4292632 {A : Type'} (s : A -> Prop) (f : A -> A) (_48647 : A) : (term423 A f s _48647) = (term426 A s f _48647).
Proof. exact (@lem4292631 (term388 A s _48647) ((term313 A f _48647) = _48647)). Qed.
Lemma lem4292634 (a : Prop) : (term24 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4292635 {A : Type'} (s : A -> Prop) (_48647 : A) : (term415 A s _48647) = (@I (A -> Prop) s _48647).
Proof. exact (@lem4292634 (@I (A -> Prop) s _48647)). Qed.
Lemma lem4292636 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4292637 {A : Type'} (s : A -> Prop) (_48647 : A) : (term416 A s _48647) = (term417 A s _48647).
Proof. exact (MK_COMB (@lem4292636) (@lem4292635 A s _48647)). Qed.
Lemma lem4292638 {A : Type'} (f : A -> A) (_48647 : A) : ((term313 A f _48647) = _48647) = ((term313 A f _48647) = _48647).
Proof. exact (eq_refl ((term313 A f _48647) = _48647)). Qed.
Lemma lem4292639 {A : Type'} (s : A -> Prop) (f : A -> A) (_48647 : A) : (term426 A s f _48647) = (term427 A s f _48647).
Proof. exact (MK_COMB (@lem4292637 A s _48647) (@lem4292638 A f _48647)). Qed.
Lemma lem4292640 {A : Type'} (s : A -> Prop) (f : A -> A) (_48647 : A) : (term423 A f s _48647) = (term427 A s f _48647).
Proof. exact (TRANS (@lem4292632 A s f _48647) (@lem4292639 A s f _48647)). Qed.
Lemma lem4292643 {A : Type'} (_48647 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term427 A s f _48647.
Proof. exact (EQ_MP (@lem4292640 A s f _48647) (@lem4292629 A _48647 f s h1)). Qed.
Lemma lem4292644 {A : Type'} (_48647 : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term427 A s f _48647.
Proof. exact (@lem4292643 A _48647 f s h1). Qed.
Lemma lem4292645 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term427 A s f x.
Proof. exact (@lem4292644 A x f s h1). Qed.
Lemma lem4292648 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : (term313 A f x) = x.
Proof. exact (@lem4292645 A x f s h1 (@lem4292596 A s f x h2)). Qed.
Lemma lem4292649 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : term428 A f x.
Proof. exact (fun h0 : term375 A f x => @lem4292648 A s f x h1 h2). Qed.
Lemma lem4292651 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292652 {A : Type'} (f : A -> A) (x : A) : (term428 A f x) = ((term313 A f x) = x).
Proof. exact (@lem4292651 ((term313 A f x) = x)). Qed.
Lemma lem4292653 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : (term313 A f x) = x.
Proof. exact (EQ_MP (@lem4292652 A f x) (@lem4292649 A s f x h1 h2)). Qed.
Lemma lem4292656 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4292658 {A : Type'} (f : A -> A) (x : A) : (term375 A f x) = (term453 A f x).
Proof. exact (@lem4292656 ((term313 A f x) = x)). Qed.
Lemma lem4292661 {A : Type'} (f : A -> A) (x : A) (h1 : term375 A f x) : term453 A f x.
Proof. exact (EQ_MP (@lem4292658 A f x) (@lem4292094 A f x h1)). Qed.
Lemma lem4292664 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term375 A f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (@lem4292661 A f x h1 (@lem4292653 A s f x h2 h3)). Qed.
Lemma lem4292665 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term375 A f x) (h2 : term323 A f s) (h3 : term177 A s f x) : term104.
Proof. exact (fun h0 : ~ False => @lem4292664 A s f x h1 h2 h3). Qed.
Lemma lem4292667 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4292668 : term104 = False.
Proof. exact (@lem4292667 False). Qed.
Lemma lem4292669 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term375 A f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (EQ_MP (@lem4292668) (@lem4292665 A s f x h1 h2 h3)). Qed.
Lemma lem4292670 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term375 A f x) (h2 : term323 A f s) (h3 : term177 A s f x) : (term375 A f x) = False.
Proof. exact (prop_ext (fun h4 : term375 A f x => @lem4292669 A s f x h1 h2 h3) (fun h4 : False => @lem4292094 A f x h1)). Qed.
Lemma lem4292671 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term375 A f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (EQ_MP (@lem4292670 A s f x h1 h2 h3) (@lem4292094 A f x h1)). Qed.
Lemma lem4292672 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) (h2 : (f x) = x) : ((f x) = x) = False.
Proof. exact (prop_ext (fun h3 : (f x) = x => @lem4292546 A s f x h1 h2) (fun h3 : False => @lem4292074 A f x h2)). Qed.
Lemma lem4292673 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4292672 A s f x h1 h2) (@lem4292074 A f x h2)). Qed.
Lemma lem4292674 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : ((term313 A f x) = (f x)) = False.
Proof. exact (prop_ext (fun h4 : (term313 A f x) = (f x) => @lem4292480 A s f x h1 h2 h3) (fun h4 : False => @lem4292054 A f x h3)). Qed.
Lemma lem4292675 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : False.
Proof. exact (EQ_MP (@lem4292674 A s f x h1 h2 h3) (@lem4292054 A f x h3)). Qed.
Lemma lem4292676 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : (term398 A s f x) = False.
Proof. exact (prop_ext (fun h4 : term398 A s f x => @lem4292225 A s f x h1 h2 h3) (fun h4 : False => @lem4292034 A s f x h1)). Qed.
Lemma lem4292677 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (EQ_MP (@lem4292676 A s f x h1 h2 h3) (@lem4292034 A s f x h1)). Qed.
Lemma lem4292678 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term375 A f x) (h2 : term323 A f s) (h3 : term177 A s f x) : (term375 A f x) = False.
Proof. exact (prop_ext (fun h4 : term375 A f x => @lem4292671 A s f x h1 h2 h3) (fun h4 : False => @lem4292006 A f x h1)). Qed.
Lemma lem4292679 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term375 A f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (EQ_MP (@lem4292678 A s f x h1 h2 h3) (@lem4292006 A f x h1)). Qed.
Lemma lem4292680 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) (h2 : (f x) = x) : ((f x) = x) = False.
Proof. exact (prop_ext (fun h3 : (f x) = x => @lem4292673 A s f x h1 h2) (fun h3 : False => @lem4291967 A f x h2)). Qed.
Lemma lem4292681 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4292680 A s f x h1 h2) (@lem4291967 A f x h2)). Qed.
Lemma lem4292682 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : ((term313 A f x) = (f x)) = False.
Proof. exact (prop_ext (fun h4 : (term313 A f x) = (f x) => @lem4292675 A s f x h1 h2 h3) (fun h4 : False => @lem4291928 A f x h3)). Qed.
Lemma lem4292683 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : False.
Proof. exact (EQ_MP (@lem4292682 A s f x h1 h2 h3) (@lem4291928 A f x h3)). Qed.
Lemma lem4292684 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : (term398 A s f x) = False.
Proof. exact (prop_ext (fun h4 : term398 A s f x => @lem4292677 A s f x h1 h2 h3) (fun h4 : False => @lem4291889 A s f x h1)). Qed.
Lemma lem4292685 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (EQ_MP (@lem4292684 A s f x h1 h2 h3) (@lem4291889 A s f x h1)). Qed.
Lemma lem4292686 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term375 A f x) (h2 : term323 A f s) (h3 : term177 A s f x) : (term375 A f x) = False.
Proof. exact (prop_ext (fun h4 : term375 A f x => @lem4292679 A s f x h1 h2 h3) (fun h4 : False => @lem4292006 A f x h1)). Qed.
Lemma lem4292687 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term375 A f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (EQ_MP (@lem4292686 A s f x h1 h2 h3) (@lem4292006 A f x h1)). Qed.
Lemma lem4292688 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) (h2 : (f x) = x) : ((f x) = x) = False.
Proof. exact (prop_ext (fun h3 : (f x) = x => @lem4292681 A s f x h1 h2) (fun h3 : False => @lem4291967 A f x h2)). Qed.
Lemma lem4292689 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term177 A s f x) (h2 : (f x) = x) : False.
Proof. exact (EQ_MP (@lem4292688 A s f x h1 h2) (@lem4291967 A f x h2)). Qed.
Lemma lem4292690 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : ((term313 A f x) = (f x)) = False.
Proof. exact (prop_ext (fun h4 : (term313 A f x) = (f x) => @lem4292683 A s f x h1 h2 h3) (fun h4 : False => @lem4291928 A f x h3)). Qed.
Lemma lem4292691 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : (term313 A f x) = (f x)) : False.
Proof. exact (EQ_MP (@lem4292690 A s f x h1 h2 h3) (@lem4291928 A f x h3)). Qed.
Lemma lem4292692 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : (term398 A s f x) = False.
Proof. exact (prop_ext (fun h4 : term398 A s f x => @lem4292685 A s f x h1 h2 h3) (fun h4 : False => @lem4291889 A s f x h1)). Qed.
Lemma lem4292693 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term398 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (EQ_MP (@lem4292692 A s f x h1 h2 h3) (@lem4291889 A s f x h1)). Qed.
Lemma lem4292694 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : term379 A f x) : False.
Proof. exact (or_elim (@lem4291846 A f x h3) (fun h0 : (f x) = x => @lem4292689 A s f x h2 h0) (fun h0 : term375 A f x => @lem4292687 A s f x h0 h1 h2)). Qed.
Lemma lem4292695 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) (h3 : term400 A s f x) : False.
Proof. exact (or_elim (@lem4291845 A s f x h3) (fun h0 : term398 A s f x => @lem4292693 A s f x h0 h1 h2) (fun h0 : (term313 A f x) = (f x) => @lem4292691 A s f x h1 h2 h0)). Qed.
Lemma lem4292696 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term364 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (or_elim (@lem4291840 A s f x h1) (fun h0 : term400 A s f x => @lem4292695 A s f x h2 h3 h0) (fun h0 : term379 A f x => @lem4292694 A s f x h2 h3 h0)). Qed.
Lemma lem4292697 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term364 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : (term177 A s f x) = False.
Proof. exact (prop_ext (fun h4 : term177 A s f x => @lem4292696 A s f x h1 h2 h3) (fun h4 : False => @lem4291695 A s f x h3)). Qed.
Lemma lem4292698 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term364 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (EQ_MP (@lem4292697 A s f x h1 h2 h3) (@lem4291695 A s f x h3)). Qed.
Lemma lem4292699 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term364 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : (term364 A s f x) = False.
Proof. exact (prop_ext (fun h4 : term364 A s f x => @lem4292698 A s f x h1 h2 h3) (fun h4 : False => @lem4291614 A s f x h1)). Qed.
Lemma lem4292700 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term364 A s f x) (h2 : term323 A f s) (h3 : term177 A s f x) : False.
Proof. exact (EQ_MP (@lem4292699 A s f x h1 h2 h3) (@lem4291614 A s f x h1)). Qed.
Lemma lem4292701 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : term363 A s f x.
Proof. exact (fun h0 : term364 A s f x => @lem4292700 A s f x h0 h1 h2). Qed.
Lemma lem4292702 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (h1 : term323 A f s) (h2 : term177 A s f x) : term341 A s f x.
Proof. exact (EQ_MP (@lem4291613 A s f x) (@lem4292701 A s f x h1 h2)). Qed.
Lemma lem4292703 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term343 A s f x.
Proof. exact (fun h0 : term177 A s f x => @lem4292702 A s f x h1 h0). Qed.
Lemma lem4292708 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term323 A f s) : term346 A s f.
Proof. exact (fun x : A => @lem4292703 A x f s h1). Qed.
Lemma lem4292709 {A : Type'} (s : A -> Prop) (f : A -> A) : term348 A s f.
Proof. exact (fun h0 : term323 A f s => @lem4292708 A f s h0). Qed.
Lemma lem4292714 {A : Type'} (f : A -> A) : term358 A f.
Proof. exact (fun s : A -> Prop => @lem4292709 A s f). Qed.
Lemma lem4292719 {A : Type'} : term362 A.
Proof. exact (fun f : A -> A => @lem4292714 A f). Qed.
Lemma lem4292720 {A : Type'} : term361 A.
Proof. exact (EQ_MP (@lem4291607 A) (@lem4292719 A)). Qed.
Lemma lem4292721 {A : Type'} (f : A -> A) : term454 A f.
Proof. exact (@lem4292720 A f). Qed.
Lemma lem4292722 {A : Type'} (f : A -> A) : (term454 A f) = (term357 A f).
Proof. exact (eq_refl (term454 A f)). Qed.
Lemma lem4292723 {A : Type'} (f : A -> A) : term357 A f.
Proof. exact (EQ_MP (@lem4292722 A f) (@lem4292721 A f)). Qed.
Lemma lem4292724 {A : Type'} (f : A -> A) (s : A -> Prop) : term455 A f s.
Proof. exact (@lem4292723 A f s). Qed.
Lemma lem4292725 {A : Type'} (s : A -> Prop) (f : A -> A) : (term455 A f s) = (term349 A s f).
Proof. exact (eq_refl (term455 A f s)). Qed.
Lemma lem4292726 {A : Type'} (s : A -> Prop) (f : A -> A) : term349 A s f.
Proof. exact (EQ_MP (@lem4292725 A s f) (@lem4292724 A f s)). Qed.
Lemma lem4292728 {A : Type'} (s : A -> Prop) (f : A -> A) : term349 A s f.
Proof. exact (@lem4291447 A s f (@lem4292726 A s f)). Qed.
Lemma lem4292729 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term350 A s f) : False.
Proof. exact (@lem4292728 A s f (@lem4291431 A s f h1)). Qed.
Lemma lem4292730 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term350 A s f) : (term350 A s f) = False.
Proof. exact (prop_ext (fun h2 : term350 A s f => @lem4292729 A s f h1) (fun h2 : False => @lem4291431 A s f h1)). Qed.
Lemma lem4292731 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term350 A s f) : False.
Proof. exact (EQ_MP (@lem4292730 A s f h1) (@lem4291431 A s f h1)). Qed.
Lemma lem4292732 {A : Type'} (s : A -> Prop) (f : A -> A) : term349 A s f.
Proof. exact (fun h0 : term350 A s f => @lem4292731 A s f h0). Qed.
Lemma lem4292733 {A : Type'} (s : A -> Prop) (f : A -> A) : term348 A s f.
Proof. exact (EQ_MP (@lem4291430 A s f) (@lem4292732 A s f)). Qed.
Lemma lem4292735 {A : Type'} (s : A -> Prop) (f : A -> A) : term347 A s f.
Proof. exact (EQ_MP (@lem4291426 A s f) (@lem4292733 A s f)). Qed.
Lemma lem4292736 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : term303 A s f.
Proof. exact (@lem4292735 A s f (@lem4291212 A f s h1 h2)). Qed.
Lemma lem4292737 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : term304 A s f.
Proof. exact (EQ_MP (@lem4291201 A f s h2) (@lem4292736 A f s h1 h2)). Qed.
Lemma lem4292738 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : term456 A s f.
Proof. exact (ex_intro (term457 A s f) f (@lem4292737 A f s h1 h2)). Qed.
Lemma lem4292739 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : term295 A s f.
Proof. exact (@lem4290953 A s f (@lem4292738 A f s h1 h2)). Qed.
Lemma lem4292740 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : (term128 A s f) = ((term128 A s f) = (term295 A s f)).
Proof. exact (EQ_MP (@lem4290949 A s f) (@lem4292739 A f s h1 h2)). Qed.
Lemma lem4292741 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : (term128 A s f) = (term225 A s f).
Proof. exact (EQ_MP (@lem4290923 A f s h2) (@lem4292740 A f s h1 h2)). Qed.
Lemma lem4292742 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : term458 A f s.
Proof. exact (conj (@lem4292741 A f s h1 h2) (@lem4290649 A f s)). Qed.
Lemma lem4292743 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : term459 A f s.
Proof. exact (ex_intro (term460 A f s) (term225 A s f) (@lem4292742 A f s h1 h2)). Qed.
Lemma lem4292744 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : (term128 A s f) = (term6 A s).
Proof. exact (@lem4289788 A f s (@lem4292743 A f s h1 h2)). Qed.
Lemma lem4292745 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term108 A s f) : term109 A s f.
Proof. exact (proj2 (@lem4289754 A s f h1)). Qed.
Lemma lem4292746 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term108 A s f) : @FINITE A s.
Proof. exact (proj1 (@lem4289754 A s f h1)). Qed.
Lemma lem4292747 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : (term109 A s f) = ((term128 A s f) = (term6 A s)).
Proof. exact (prop_ext (fun h3 : term109 A s f => @lem4292744 A f s h1 h2) (fun h3 : (term128 A s f) = (term6 A s) => @lem4289755 A s f h1)). Qed.
Lemma lem4292748 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : (term128 A s f) = (term6 A s).
Proof. exact (EQ_MP (@lem4292747 A f s h1 h2) (@lem4289755 A s f h1)). Qed.
Lemma lem4292749 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : (@FINITE A s) = ((term128 A s f) = (term6 A s)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4292748 A f s h1 h2) (fun h3 : (term128 A s f) = (term6 A s) => @lem4289756 A s h2)). Qed.
Lemma lem4292750 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term109 A s f) (h2 : @FINITE A s) : (term128 A s f) = (term6 A s).
Proof. exact (EQ_MP (@lem4292749 A f s h1 h2) (@lem4289756 A s h2)). Qed.
Lemma lem4292751 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : @FINITE A s) (h2 : term108 A s f) : (term109 A s f) = ((term128 A s f) = (term6 A s)).
Proof. exact (prop_ext (fun h3 : term109 A s f => @lem4292750 A f s h3 h1) (fun h3 : (term128 A s f) = (term6 A s) => @lem4292745 A s f h2)). Qed.
Lemma lem4292752 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : @FINITE A s) (h2 : term108 A s f) : (term128 A s f) = (term6 A s).
Proof. exact (EQ_MP (@lem4292751 A s f h1 h2) (@lem4292745 A s f h2)). Qed.
Lemma lem4292753 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term108 A s f) : (@FINITE A s) = ((term128 A s f) = (term6 A s)).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem4292752 A s f h2 h1) (fun h2 : (term128 A s f) = (term6 A s) => @lem4292746 A s f h1)). Qed.
Lemma lem4292754 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term108 A s f) : (term128 A s f) = (term6 A s).
Proof. exact (EQ_MP (@lem4292753 A s f h1) (@lem4292746 A s f h1)). Qed.
Lemma lem4292755 {A : Type'} (f : A -> A) (s : A -> Prop) : term461 A f s.
Proof. exact (fun h0 : term108 A s f => @lem4292754 A s f h0). Qed.
Lemma lem4292760 {A : Type'} (f : A -> A) : term462 A f.
Proof. exact (fun s : A -> Prop => @lem4292755 A f s). Qed.
Lemma lem4292765 {A : Type'} : term463 A.
Proof. exact (fun f : A -> A => @lem4292760 A f). Qed.
